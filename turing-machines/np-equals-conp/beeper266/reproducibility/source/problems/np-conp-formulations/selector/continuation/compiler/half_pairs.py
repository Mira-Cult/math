"""Specialize a fused quotient/remainder pair by two to the paid half kernel.

The inherited fused assignment always calls its general division kernel, even
for the literal two.  The half kernel is already used by scalar division/parity
and in-place halving; this rule shares it with simultaneous divrem assignments.
"""
import ast
from contextual_tree_build import ContextualTreeBuilder


class HalfPairBuilder(ContextualTreeBuilder):
    def __init__(self, *args, **kwargs):
        super().__init__(*args, **kwargs)
        self.half_pair_certificate = []

    def block(self, frame, statements, loops=()):
        code = []
        for node in statements:
            match = self.divrem_assignment(node)
            if (match is None or not isinstance(match[2], ast.Constant)
                    or type(match[2].value) is not int or match[2].value != 2):
                code += super().block(frame, [node], loops)
                continue
            targets, left, divisor = match
            src = self.variable(frame, left.id)
            consume = left.id in {target.id for target in targets}
            A, B, Q, R, C = self.micro
            code += self.load_operand(A, ('consume' if consume else 'reference', src))
            code += [self.half_kernel()]
            for target, result in zip(targets, (R, Q)):
                destination = self.variable(frame, target.id)
                if not (consume and destination == src):
                    code += [self.clear(destination)]
                code += [self.move(destination, result)]
            self.half_pair_certificate.append(dict(function=frame['name'],
                line=getattr(node, 'lineno', None), dividend=left.id,
                targets=[target.id for target in targets], divisor=2,
                consumed=consume, kernel='half_kernel',
                output_order=['remainder', 'quotient']))
        return code
