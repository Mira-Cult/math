"""Selected record accumulator is zero after the exact ordinal-drain loop."""
import ast
from contextlib import contextmanager


def match(statements):
    if len(statements)<4:return None
    loop=statements[0]
    if not isinstance(loop,ast.While) or not isinstance(loop.test,ast.Name) or loop.orelse:return None
    import lower_half
    pop=lower_half.match_pop(statements[1:])
    if pop is None:return None
    R,D=pop
    if loop.test.id!=R or R==D:return None
    desired=ast.parse(f'while {R}:\n    {R}-=1\n    while {D}%2:\n        {D}//=2\n    {D}//=2').body[0]
    if ast.dump(loop,include_attributes=False)!=ast.dump(desired,include_attributes=False):return None
    return R,D


@contextmanager
def installed():
    import lower_half
    old=lower_half.NativeHalfMixin.block
    builders=[]
    def block(self,frame,statements,loops=()):
        code=[];index=0
        if not hasattr(self,'zero_pop_certificate'):
            self.zero_pop_certificate=[];builders.append(self)
        while index<len(statements):
            names=match(statements[index:])
            if names is None:
                end=index+1
                while end<len(statements) and match(statements[end:]) is None:end+=1
                code+=old(self,frame,statements[index:end],loops);index=end;continue
            R,D=[self.variable(frame,name) for name in names]
            assert R!=D
            code+=old(self,frame,[statements[index]],loops)
            label=self.fresh('zero_accumulator_record')
            code+=[self.label(label,[self.half_operation(D),[R.inc,'continue_'+label]])]
            self.zero_pop_certificate.append(dict(function=frame['name'],line=statements[index].lineno,
                exact_ast=[ast.dump(x,include_attributes=False) for x in statements[index:index+4]],
                ordinal_and_result=str(R),stream=str(D),
                entry='R,D distinct; arbitrary finite R,D; unchanged ordinal-drain entry',
                intermediate='ordinal loop exits only through its zero test: R=0; no increment or assignment to R inside loop',
                exit='selected record length in R; D is residual after its real or virtual terminating zero',
                removed='only the redundant clear of R between proven-zero ordinal drain and selected pop',
                progress='finite ordinal decreases; each skip and selected unary pop consumes finite ones and a terminating real/virtual zero'))
            index+=4
        return code
    lower_half.NativeHalfMixin.block=block
    try:yield builders
    finally:lower_half.NativeHalfMixin.block=old
