"""Exact natural-number guard with an immediately consumed leading unit.

For every natural x, `if x: x -= 1; body else: other` is one DECNZ
followed by the selected body. No Boolean assumption or new operation is used.
"""
import ast
from contextlib import contextmanager
import build_experiment

lower_half=build_experiment.build_parser.lower_half


def match(node):
    if not (isinstance(node,ast.If) and isinstance(node.test,ast.Name) and node.body):
        return None
    first=node.body[0]
    if not (isinstance(first,ast.AugAssign) and isinstance(first.target,ast.Name)
            and first.target.id==node.test.id and isinstance(first.op,ast.Sub)
            and isinstance(first.value,ast.Constant) and type(first.value.value) is int
            and first.value.value==1):
        return None
    return node.test.id


@contextmanager
def installed():
    original=lower_half.NativeHalfMixin.block
    def block(self,frame,statements,loops=()):
        code,pending=[],[]
        if not hasattr(self,'consume_guard_certificate'):self.consume_guard_certificate=[]
        for node in statements:
            name=match(node)
            if name is None:
                pending.append(node);continue
            if pending:code+=original(self,frame,pending,loops);pending=[]
            operand=self.variable(frame,name)
            label=self.fresh('consumed_positive_guard')
            yes=self.block(frame,node.body[1:],loops)
            no=self.block(frame,node.orelse,loops)
            code += [self.label(label,[[operand.decnz,[yes,'break_'+label]],no])]
            self.consume_guard_certificate.append(dict(function=frame['name'],line=node.lineno,
                operand=str(operand),exact_ast=ast.dump(node,include_attributes=False),
                contract='all naturals: zero stays zero and takes else; positive x becomes x-1 and takes body after its first statement',
                ownership='single existing operand operation; source boundary after leading decrement; inherited fresh primitive zero-peer checks',
                progress='one positive finite DECNZ segment, then exactly one admitted source branch'))
        if pending:code+=original(self,frame,pending,loops)
        return code
    lower_half.NativeHalfMixin.block=block
    try:yield
    finally:lower_half.NativeHalfMixin.block=original
