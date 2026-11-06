"""Source-to-native-half lowering; mathematical source is unchanged."""
import ast
from TMBuilder import subroutine
from record_pop import match_pop
import half_engine


class NativeHalfMixin:
    def __init__(self, *args, **kwargs):
        super().__init__(*args, **kwargs)
        self.native_half_registers = set()
        self.native_half_certificate = []

    def half_operation(self, register):
        self.native_half_registers.add(register)
        return half_engine.operation(register)

    @subroutine
    def half_kernel(self):
        A, B, Q, R, C = self.micro
        return [[self.half_operation(A), R.inc], self.move(Q, A)]

    def block(self, frame, statements, loops=()):
        code, index = [], 0
        while index < len(statements):
            matched = match_pop(statements[index:])
            if matched is not None:
                count, stream = matched
                result, source = self.variable(frame, count), self.variable(frame, stream)
                if result == source:
                    raise ValueError('native record pop requires distinct output and stream')
                label = self.fresh('native_record')
                code += [self.clear(result), self.label(label, [self.half_operation(source),
                         [result.inc, 'continue_'+label]])]
                self.native_half_certificate.append(dict(function=frame['name'],
                    line=statements[index].lineno, kind='record-pop',
                    source=str(source), result=str(result)))
                index += 3
                continue
            node = statements[index]
            pair = self.divrem_assignment(node)
            if (pair is not None and isinstance(pair[2], ast.Constant)
                    and type(pair[2].value) is int and pair[2].value == 2
                    and pair[0][1].id == pair[1].id):
                targets, left, _ = pair
                source = self.variable(frame, left.id)
                remainder = self.variable(frame, targets[0].id)
                if source == remainder:
                    raise ValueError('native pair requires distinct quotient and remainder')
                code += [self.clear(remainder), [self.half_operation(source), remainder.inc]]
                self.native_half_certificate.append(dict(function=frame['name'],
                    line=node.lineno, kind='quotient-remainder',
                    source=str(source), remainder=str(remainder)))
            else:
                code += super().block(frame, [node], loops)
            index += 1
        return code

    def build_tree(self):
        return super().build_tree()

    def generate(self):
        super().generate()
        half_engine.install(self)
