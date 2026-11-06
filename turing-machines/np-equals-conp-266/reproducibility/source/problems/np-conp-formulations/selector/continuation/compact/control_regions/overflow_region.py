"""Exact finite witness-bound guard with native half and optional clock borrowing."""
import ast
from contextlib import contextmanager
from itertools import combinations


def match(statements):
    if len(statements)<3:return None
    a,b,c=statements[:3]
    if not (isinstance(a,ast.Assign) and len(a.targets)==1 and isinstance(a.targets[0],ast.Name)
        and isinstance(a.value,ast.Name) and isinstance(b,ast.Assign) and len(b.targets)==1
        and isinstance(b.targets[0],ast.Name) and isinstance(b.value,ast.Name)):
        return None
    D,B,S,C=a.targets[0].id,a.value.id,b.targets[0].id,b.value.id
    if len({D,B,S,C})!=4:return None
    wanted=ast.parse(f'{D}={B}\n{S}={C}\nwhile {S}:\n    {S}-=1\n    {D}//=2').body
    if [ast.dump(x,include_attributes=False) for x in statements[:3]]!=[ast.dump(x,include_attributes=False) for x in wanted]:return None
    return D,B,S,C


@contextmanager
def installed(mode):
    import lower_half,live_registers
    old=lower_half.NativeHalfMixin.block;interf=live_registers.interference
    builders=[]
    def interference(function,registers,returns,retained_resets,reuse_returns):
        cfg,graph=interf(function,registers,returns,retained_resets,reuse_returns)
        records=[]
        for node in ast.walk(function):
            for _,value in ast.iter_fields(node):
                if not isinstance(value,list) or not all(isinstance(x,ast.stmt) for x in value):continue
                for i in range(len(value)-2):
                    names=match(value[i:])
                    if names is None:continue
                    for x,y in combinations(names,2):graph[x].add(y);graph[y].add(x)
                    records.append(dict(line=value[i].lineno,operands=list(names),reason='closed overflow guard borrows/restores clock while preserving witness master'))
        if records:cfg['overflow_guard_interference']=records
        return cfg,graph
    def block(self,frame,statements,loops=()):
        code=[];index=0
        if not hasattr(self,'overflow_guard_certificate'):
            self.overflow_guard_certificate=[]
            builders.append(self)
        while index<len(statements):
            names=match(statements[index:])
            if names is None:
                end=index+1
                while end<len(statements) and match(statements[end:]) is None:end+=1
                code+=old(self,frame,statements[index:end],loops);index=end;continue
            D,B,S,C=[self.variable(frame,name) for name in names]
            assert len({D,B,S,C})==4
            half=[[self.half_operation(D),'_break.0']]
            if mode=='borrow':
                code += [self.clear(D),self.copy(D,B),self.clear(S),
                    self.while_decnz(C,[S.inc,half]),self.move(C,S)]
            elif mode=='native':
                code += [self.clear(D),self.copy(D,B),self.clear(S),self.copy(S,C),
                    self.while_decnz(S,half)]
            else:raise ValueError(mode)
            self.overflow_guard_certificate.append(dict(function=frame['name'],line=statements[index].lineno,
                mode=mode,exact_ast=[ast.dump(x,include_attributes=False) for x in statements[index:index+3]],
                result=str(D),witness=str(B),steps=str(S),clock=str(C),copy_scratch=str(self.scratch),
                entry='D,B,S,C distinct; B,C natural; copy scratch zero; stale D,S arbitrary',
                invariant='after t halves D=floor(old_B/2^t); borrowed C=old_C-t and S=t, or copied S=old_C-t',
                exit='D=floor(old_B/2^old_C); S=0; B,C restored; other values and copy scratch preserved',
                progress='finite stale resets and copy, finite clock countdown, finite native HALF and optional clock restore'))
            index+=3
        return code
    lower_half.NativeHalfMixin.block=block;live_registers.interference=interference
    try:yield builders
    finally:lower_half.NativeHalfMixin.block=old;live_registers.interference=interf
