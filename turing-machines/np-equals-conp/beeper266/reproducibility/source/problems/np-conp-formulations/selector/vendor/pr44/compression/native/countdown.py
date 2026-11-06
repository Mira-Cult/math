"""Opt-in source countdown lowering to the inherited native DECNZ primitive.

Only `while x: x -= 1; body` with a named guard and no while-else matches.
The source AST and its conservative liveness analysis are left unchanged.
"""
from pathlib import Path
import ast,sys
HERE=Path(__file__).resolve().parent
ROOT=HERE.parents[1]
sys.path.insert(0,str(ROOT/'compression/grammar'))
from fused_horner import HornerBuilder,GenericHornerBuilder


class CountdownMixin:
    def __init__(self,*args,countdown_loops=True,**kwargs):
        if type(countdown_loops) is not bool:raise TypeError('countdown_loops must be a bool')
        super().__init__(*args,**kwargs)
        self.countdown_loops=countdown_loops
        self.countdown_certificate=[]

    def block(self,frame,statements,loops=()):
        if not self.countdown_loops:return super().block(frame,statements,loops)
        code=[]
        for node in statements:
            match=False
            if (isinstance(node,ast.While) and not node.orelse
                    and isinstance(node.test,ast.Name) and node.body):
                first=node.body[0]
                match=(isinstance(first,ast.AugAssign)
                    and isinstance(first.target,ast.Name)
                    and first.target.id==node.test.id
                    and isinstance(first.op,ast.Sub)
                    and isinstance(first.value,ast.Constant)
                    and type(first.value.value) is int and first.value.value==1)
            if not match:
                code+=super().block(frame,[node],loops)
                continue
            counter=self.variable(frame,node.test.id)
            label=self.fresh('countdown')
            body=self.block(frame,node.body[1:],loops+(label,))
            code += [self.label(label,[counter.decnz,[body,'continue_'+label]])]
            self.countdown_certificate.append(dict(function=frame['name'],
                line=getattr(node,'lineno',None),variable=node.test.id,
                guard='named natural variable',decrement=1,while_else=False,
                body_reassignments_allowed=True))
        return code


class CountdownHornerBuilder(CountdownMixin,HornerBuilder):
    pass


class GenericCountdownHornerBuilder(CountdownMixin,GenericHornerBuilder):
    pass
