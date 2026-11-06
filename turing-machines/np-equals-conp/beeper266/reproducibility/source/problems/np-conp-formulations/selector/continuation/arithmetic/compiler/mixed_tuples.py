"""Direct small literals in an otherwise parallel tuple assignment.

All nonliteral RHS values are still captured before any destination write.
Only the zero-owned temporary for a pure literal is omitted.
"""
import ast
from contextlib import contextmanager

from optimized_natural import small


def match_mixed(node):
    if not (isinstance(node, ast.Assign) and len(node.targets) == 1
            and isinstance(node.targets[0], ast.Tuple)
            and isinstance(node.value, (ast.Tuple, ast.List))):
        return None
    targets, values = node.targets[0].elts, node.value.elts
    if (len(targets) != len(values) or len(targets) < 2
            or not all(isinstance(target, ast.Name) for target in targets)
            or len({target.id for target in targets}) != len(targets)):
        return None
    literals = [small(value) for value in values]
    if not any(value is not None for value in literals) or all(value is not None for value in literals):
        return None
    return targets, values, literals


class MixedTupleMixin:
    def __init__(self, *args, **kwargs):
        super().__init__(*args, **kwargs)
        self.mixed_tuple_certificate = []

    def block(self, frame, statements, loops=()):
        code, pending = [], []
        for node in statements:
            matched = match_mixed(node)
            if matched is None:
                pending.append(node)
                continue
            if pending:
                code += super().block(frame, pending, loops)
                pending = []
            targets, values, literals = matched
            captured = []
            for value, literal in zip(values, literals):
                if literal is not None:
                    captured.append(None)
                else:
                    part, result = self.expression(frame, value)
                    code += part
                    captured.append(result)
            for target, literal, captured_value in zip(targets, literals, captured):
                destination = self.variable(frame, target.id)
                code += [self.clear(destination)]
                if literal is not None:
                    code += [destination.inc]*literal
                else:
                    code += [self.move(destination, captured_value)]
                    self.free(frame, captured_value)
            self.mixed_tuple_certificate.append(dict(function=frame['name'],
                line=getattr(node, 'lineno', None), targets=[target.id for target in targets],
                literal_values=literals, captured_rhs=sum(value is None for value in literals),
                elided_literal_temporaries=sum(value is not None for value in literals),
                evaluation='all nonliteral RHS captured left-to-right before any destination write'))
        if pending:
            code += super().block(frame, pending, loops)
        return code


@contextmanager
def installed(integrated):
    original = integrated.ArithmeticBuilder
    class MixedArithmetic(MixedTupleMixin, original):
        pass
    integrated.ArithmeticBuilder = MixedArithmetic
    try:
        yield
    finally:
        integrated.ArithmeticBuilder = original
