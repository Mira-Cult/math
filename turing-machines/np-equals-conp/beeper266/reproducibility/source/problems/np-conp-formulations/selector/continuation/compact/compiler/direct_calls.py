"""Direct installation of pure procedure-call arguments.

The frozen compiler stages every argument in a caller-owned temporary.  This
extension removes that stage for names and natural constants, only when the
entire argument group has no call and no source-destructive read.  Complex
arguments remain captured before any callee parameter is changed.  The
existing acyclic call-height allocation keeps caller and callee cells apart.
"""
from __future__ import annotations

import ast
from contextlib import contextmanager


class DirectCallMixin:
    def __init__(self, *args, direct_calls=True, **kwargs):
        super().__init__(*args, **kwargs)
        self.direct_calls = direct_calls
        self.direct_call_certificate = []

    def call(self, frame, node):
        result = self.direct_call(frame, node)
        return super().call(frame, node) if result is None else result

    def eligible_direct_call(self, node):
        if not self.direct_calls or not self.consuming_returns:
            return False
        if (not isinstance(node.func, ast.Name) or node.keywords
                or node.func.id == 'main'):
            return False
        descendants = [child for argument in node.args
                       for child in ast.walk(argument)]
        if (any(isinstance(child, ast.Call) for child in descendants)
                or any(isinstance(child, ast.Name)
                       and id(child) in self.live.consume
                       for child in descendants)):
            return False
        return any(isinstance(argument, ast.Name)
                   or isinstance(argument, ast.Constant)
                   and isinstance(argument.value, (int, bool))
                   and argument.value >= 0 for argument in node.args)

    def direct_call(self, frame, node, *, capture_returns=True):
        if not self.eligible_direct_call(node):
            return None
        descendants = [child for argument in node.args
                       for child in ast.walk(argument)]
        simple = [isinstance(argument, ast.Name)
                  or isinstance(argument, ast.Constant)
                  and isinstance(argument.value, (int, bool))
                  and argument.value >= 0
                  for argument in node.args]
        body, callee = self.compile_function(node.func.id)
        if len(node.args) != len(callee['args']):
            raise ValueError('argument count mismatch')
        if self.heights[frame['name']] <= self.heights[callee['name']]:
            raise ValueError('direct call requires distinct acyclic call heights')

        destinations = [self.variable(callee, name) for name in callee['args']]
        reads = {self.variable(frame, child.id) for child in descendants
                 if isinstance(child, ast.Name) and isinstance(child.ctx, ast.Load)}
        if len(set(destinations)) != len(destinations) or set(destinations) & reads:
            raise ValueError('callee parameters must be disjoint from caller reads')

        code, captured = [], []
        for argument, is_simple in zip(node.args, simple):
            if is_simple:
                kind = 'reference' if isinstance(argument, ast.Name) else 'constant'
                data = (self.variable(frame, argument.id) if kind == 'reference'
                        else int(argument.value))
                captured.append((kind, data))
            else:
                part, value = self.expression(frame, argument)
                code += part
                captured.append(('owned', value))
        owned = {value for kind, value in captured if kind == 'owned'}
        if set(destinations) & (owned | set(self.micro) | {self.scratch}):
            raise ValueError('callee parameters overlap compiler-owned storage')
        for target, value in zip(destinations, captured):
            code += [self.clear(target)] + self.load_operand(target, value)
            if value[0] == 'owned':
                self.free(frame, value[1])
        code += [body]
        outputs = list(callee['returns'])
        if capture_returns:
            outputs = []
            for result in callee['returns']:
                out = self.alloc(frame)
                code += [self.move(out, result)]
                outputs.append(out)
        self.direct_call_certificate.append(dict(
            caller=frame['name'], callee=callee['name'],
            line=getattr(node, 'lineno', None),
            caller_height=self.heights[frame['name']],
            callee_height=self.heights[callee['name']],
            argument_kinds=[kind for kind, _ in captured],
            parameter_cells=list(map(str, destinations)),
            source_read_cells=sorted(map(str, reads)),
            elided_argument_temporaries=sum(simple),
            capture_returns=capture_returns,
            complex_evaluation='left-to-right before all parameter installation',
            source_reads='call-free and no destructive source-read markers'))
        return code, outputs


@contextmanager
def installed(integrated):
    original = integrated.ArithmeticBuilder
    class DirectArithmetic(DirectCallMixin, original):
        pass
    integrated.ArithmeticBuilder = DirectArithmetic
    try:
        yield
    finally:
        integrated.ArithmeticBuilder = original
