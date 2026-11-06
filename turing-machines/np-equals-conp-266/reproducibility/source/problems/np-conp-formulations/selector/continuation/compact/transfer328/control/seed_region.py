"""Build the complete certificate countdown in place and restore its clock."""
import ast
from contextlib import contextmanager
from itertools import combinations
import clock_region
from clock_region import lower_half,live_registers


def match(statements):
    if len(statements)<3:return None
    first,second,third=statements[:3]
    if not (isinstance(first,ast.Assign) and len(first.targets)==1 and isinstance(first.targets[0],ast.Name)
            and isinstance(second,ast.Assign) and len(second.targets)==1 and isinstance(second.targets[0],ast.Name)
            and isinstance(second.value,ast.Name)):
        return None
    F,S,K=first.targets[0].id,second.targets[0].id,second.value.id
    if len({F,S,K})!=3:return None
    expected=ast.parse(f'{F} = 1\n{S} = {K}\nwhile {S}:\n    {S} -= 1\n    {F} *= 2').body
    if [ast.dump(x,include_attributes=False) for x in statements[:3]] != [ast.dump(x,include_attributes=False) for x in expected]:
        return None
    return F,S,K


@contextmanager
def installed():
    original_block=lower_half.NativeHalfMixin.block
    original_interference=live_registers.interference

    def interference(function,registers,returns,retained_resets,reuse_returns):
        cfg,graph=original_interference(function,registers,returns,retained_resets,reuse_returns)
        constraints=[]
        for node in ast.walk(function):
            for _,value in ast.iter_fields(node):
                if not isinstance(value,list) or not all(isinstance(x,ast.stmt) for x in value):continue
                for i in range(len(value)-2):
                    names=match(value[i:])
                    if names is None:continue
                    for left,right in combinations(names,2):
                        assert left in graph and right in graph
                        graph[left].add(right);graph[right].add(left)
                    constraints.append(dict(line=value[i].lineno,operands=list(names),
                        reason='simultaneous certificate count, clock restore counter and borrowed clock'))
        if constraints:cfg['closed_seed_interference']=constraints
        return cfg,graph

    def block(self,frame,statements,loops=()):
        code=[];index=0
        if not hasattr(self,'certificate_seed_certificate'):self.certificate_seed_certificate=[]
        while index<len(statements):
            names=match(statements[index:])
            if names is None:
                end=index+1
                while end<len(statements) and match(statements[end:]) is None:end+=1
                code+=original_block(self,frame,statements[index:end],loops);index=end;continue
            F,S,K=[self.variable(frame,name) for name in names]
            Q=self.micro[2]
            assert len({F,S,K,Q})==4
            code += [self.clear(F),F.inc,self.clear(S),
                self.while_decnz(K,[S.inc,
                    self.while_decnz(F,[Q.inc,Q.inc]),self.move(F,Q)]),
                self.move(K,S)]
            self.certificate_seed_certificate.append(dict(function=frame['name'],line=statements[index].lineno,
                exact_ast=[ast.dump(x,include_attributes=False) for x in statements[index:index+3]],
                output=str(F),restore_counter=str(S),clock_master=str(K),double_work=str(Q),
                entry='four distinct logical operands; arbitrary old output/restore; clock natural; double work zero',
                invariant='after t doublings output=2^t, clock=old_clock-t, restore=t, work=0',
                exit='output=2^old_clock; clock restored; restore/work zero; all other logical cells preserved',
                progress='finite output/restore resets; decreasing clock; finite old-output doubling; finite clock restoration',
                scope='exact three-statement source block; C=0 gives one empty-certificate attempt; no new physical primitive'))
            index+=3
        return code

    lower_half.NativeHalfMixin.block=block
    live_registers.interference=interference
    try:yield
    finally:
        lower_half.NativeHalfMixin.block=original_block
        live_registers.interference=original_interference
