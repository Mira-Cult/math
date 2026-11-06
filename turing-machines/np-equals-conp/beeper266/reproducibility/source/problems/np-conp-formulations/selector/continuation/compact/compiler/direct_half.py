"""Experimental paired decrement directly on a quotient source register."""
import ast
from contextlib import contextmanager

from TMBuilder import subroutine


class DirectHalfMixin:
    def __init__(self, *args, direct_half=False, **kwargs):
        super().__init__(*args, **kwargs)
        self.direct_half = direct_half
        self.direct_half_certificate = []

    @subroutine
    def direct_half_pair(self, source, remainder):
        Q = self.micro[2]
        return [self.clear(remainder), self.label('direct_half_pairs', [
            source.decnz,
            [[source.decnz, [Q.inc, 'continue_direct_half_pairs']], remainder.inc]]),
            self.move(source, Q)]

    def block(self, frame, statements, loops=()):
        if not self.direct_half:
            return super().block(frame, statements, loops)
        code = []
        for node in statements:
            match = self.divrem_assignment(node)
            if (match is None or not isinstance(match[2], ast.Constant)
                    or type(match[2].value) is not int or match[2].value != 2
                    or match[0][1].id != match[1].id):
                code += super().block(frame, [node], loops)
                continue
            targets, left, _ = match
            source = self.variable(frame, left.id)
            remainder = self.variable(frame, targets[0].id)
            if len({source, remainder, self.micro[2]}) != 3:
                raise ValueError('direct half requires separate source, remainder and quotient work')
            code += [self.direct_half_pair(source, remainder)]
            self.direct_half_certificate.append(dict(function=frame['name'],
                line=getattr(node, 'lineno', None), dividend=left.id,
                quotient=targets[1].id, remainder=targets[0].id,
                source_cell=str(source), remainder_cell=str(remainder),
                work_cell=str(self.micro[2]),
                contract='consume source pairs into Q; odd unit into cleared remainder; move Q back'))
        return code


@contextmanager
def installed(integrated):
    original = integrated.ArithmeticBuilder
    class DirectHalfArithmetic(DirectHalfMixin, original):
        pass
    integrated.ArithmeticBuilder = DirectHalfArithmetic
    try:
        yield
    finally:
        integrated.ArithmeticBuilder = original
