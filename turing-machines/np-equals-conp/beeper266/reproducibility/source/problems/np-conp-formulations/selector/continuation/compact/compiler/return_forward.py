"""Consume the final scalar call result directly in an equality guard.

The left operand is evaluated first and remains owned or in the caller frame.
The right call is the last effectful computation before both operand loads, so
its return slot cannot be overwritten by another call.  Only pure direct-call
arguments admitted by DirectCallMixin are selected here.
"""
import ast
from contextlib import contextmanager


class ReturnForwardMixin:
    def __init__(self, *args, return_forward=True, **kwargs):
        super().__init__(*args, **kwargs)
        self.return_forward = return_forward
        self.return_forward_certificate = []

    def direct_condition(self, frame, node):
        if (not self.return_forward or not isinstance(node, ast.Compare)
                or len(node.ops) != 1 or not isinstance(node.ops[0], (ast.Eq, ast.NotEq))
                or not isinstance(node.comparators[0], ast.Call)
                or not self.eligible_direct_call(node.comparators[0])):
            return super().direct_condition(frame, node)
        code, left = self.operand(frame, node.left)
        more, outputs = self.direct_call(frame, node.comparators[0], capture_returns=False)
        if len(outputs) != 1:
            raise ValueError('a scalar equality operand needs one return value')
        result = outputs[0]
        A, B, Q, R, C = self.micro
        if result in {A, B, Q, R, C, self.scratch}:
            raise ValueError('callee return slot overlaps arithmetic storage')
        if left[0] != 'constant' and left[1] == result:
            raise ValueError('earlier equality operand aliases the final return slot')
        code += more + self.load_operand(A, left) + [self.move(B, result), self.equality_kernel()]
        if left[0] == 'owned':
            self.free(frame, left[1])
        condition = Q
        if isinstance(node.ops[0], ast.NotEq):
            code += [self.if_zero(Q, A.inc), self.clear(Q)]
            condition = A
        self.return_forward_certificate.append(dict(
            caller=frame['name'], callee=node.comparators[0].func.id,
            line=getattr(node, 'lineno', None), return_slot=str(result),
            direct_destination=str(B), operator=type(node.ops[0]).__name__,
            left_operand_kind=left[0],
            order='left operand; right call; left load; consume right return; equality'))
        return code, condition


@contextmanager
def installed(integrated):
    original = integrated.ArithmeticBuilder
    class ReturnForwardArithmetic(ReturnForwardMixin, original):
        pass
    integrated.ArithmeticBuilder = ReturnForwardArithmetic
    try:
        yield
    finally:
        integrated.ArithmeticBuilder = original
