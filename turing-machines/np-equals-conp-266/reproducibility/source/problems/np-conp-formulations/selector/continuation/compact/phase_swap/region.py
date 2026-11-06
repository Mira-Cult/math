"""Exact orientation swap with three transfers through one zero work cell."""
from contextlib import contextmanager
from pathlib import Path
import ast
import sys

HERE=Path(__file__).resolve().parent
COMPACT=HERE.parent
sys.path.insert(0,str(COMPACT/'transfer328/coordinator'))
import build_experiment

lower_half=build_experiment.build_parser.lower_half


def match(node):
    if not (isinstance(node,ast.Assign) and len(node.targets)==1
            and isinstance(node.targets[0],ast.Tuple) and len(node.targets[0].elts)==2
            and isinstance(node.value,ast.Tuple) and len(node.value.elts)==2
            and all(isinstance(x,ast.Name) for x in node.targets[0].elts+node.value.elts)):
        return None
    left,right=[x.id for x in node.targets[0].elts]
    names=[x.id for x in node.value.elts]
    return (left,right) if left!=right and names==[right,left] else None


@contextmanager
def installed():
    original=lower_half.NativeHalfMixin.block
    def block(self,frame,statements,loops=()):
        code,pending=[],[]
        if not hasattr(self,'three_move_swap_certificate'):self.three_move_swap_certificate=[]
        for statement in statements:
            names=match(statement)
            if names is None:
                pending.append(statement);continue
            if pending:code+=original(self,frame,pending,loops);pending=[]
            left,right=[self.variable(frame,name) for name in names]
            work=self.micro[2]
            assert len({left,right,work})==3
            code += [self.move(work,left),self.move(left,right),self.move(right,work)]
            self.three_move_swap_certificate.append(dict(function=frame['name'],line=statement.lineno,
                exact_ast=ast.dump(statement,include_attributes=False),left=str(left),right=str(right),work=str(work),
                entry='three distinct logical carriers; arbitrary natural left and right; work zero',
                boundaries=['(L,R,Q)=(0,old_R,old_L)','(L,R,Q)=(old_R,0,old_L)','(L,R,Q)=(old_R,old_L,0)'],
                primitives='three existing terminating additive transfers; no new physical primitive or atomic alias',
                ownership='source simultaneous destinations remain distinct; fresh intermediate zero-peer/class-sum checks include work',
                progress='each transfer decreases its finite source; no event or source escape; all other logical cells preserved'))
        if pending:code+=original(self,frame,pending,loops)
        return code
    lower_half.NativeHalfMixin.block=block
    try:yield
    finally:lower_half.NativeHalfMixin.block=original
