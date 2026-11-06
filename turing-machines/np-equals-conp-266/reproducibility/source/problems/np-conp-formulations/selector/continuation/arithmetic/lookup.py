"""Guarded complete unary-record lookup over the existing natural registers.

The new kernel keeps the finite stream, record countdown and decoded value in
three reserved cells across the nested scan. Q/R are the half kernel's scratch.
It restores every source output, including the zero-record-count boundary.
"""
import ast
from record_pop import literal, match_pop
from live_registers import function_cfg


def lookup_pattern(statements):
    if len(statements) < 2:
        return None
    assignment, loop = statements[:2]
    if not (isinstance(assignment, ast.Assign) and len(assignment.targets) == 1
            and isinstance(assignment.targets[0], ast.Tuple)
            and isinstance(assignment.value, ast.Tuple)
            and len(assignment.targets[0].elts) == len(assignment.value.elts) == 2
            and all(isinstance(x, ast.Name) for x in assignment.targets[0].elts)
            and isinstance(assignment.value.elts[0], ast.Name)
            and not any(isinstance(x, ast.Call) for x in ast.walk(assignment.value.elts[1]))
            and isinstance(loop, ast.While) and not loop.orelse
            and isinstance(loop.test, ast.Name) and len(loop.body) == 4):
        return None
    stream, position = (x.id for x in assignment.targets[0].elts)
    program = assignment.value.elts[0].id
    if loop.test.id != position:
        return None
    def decrement(node):
        return (isinstance(node, ast.AugAssign) and isinstance(node.target, ast.Name)
                and node.target.id == position and isinstance(node.op, ast.Sub)
                and literal(node.value, 1))
    if decrement(loop.body[0]):
        pop = match_pop(loop.body[1:])
    elif decrement(loop.body[-1]):
        pop = match_pop(loop.body[:3])
    else:
        return None
    if pop is None or pop[1] != stream:
        return None
    result = pop[0]
    if len({stream, position, program, result}) != 4:
        return None
    return program, assignment.value.elts[1], stream, position, result


class LookupMixin:
    def __init__(self, *args, lookup_dead_outputs=True, **kwargs):
        super().__init__(*args, **kwargs)
        self.lookup_dead_outputs = lookup_dead_outputs
        self.lookup_certificate = []

    def block(self, frame, statements, loops=()):
        code = []
        index = 0
        while index < len(statements):
            pattern = lookup_pattern(statements[index:])
            if pattern is None:
                code += super().block(frame, [statements[index]], loops)
                index += 1
                continue
            program, address, stream_name, position_name, result_name = pattern
            # Evaluate the old address expression before any source output is
            # overwritten. Its whole-tuple liveness still protects program's
            # delayed input read, including repeated references in address.
            part, old_address = self.expression(frame, address)
            code += part
            # A dead source output need not have a physical cell. The explicit
            # source CFG proves no later read occurs before a new definition.
            cfg = function_cfg(self.functions[frame['name']])
            guards = [node for node in cfg['nodes']
                      if node['kind'] == 'while' and node['line'] == statements[index+1].lineno]
            assert len(guards) == 1, 'ambiguous source loop location'
            after = cfg['nodes'][guards[0]['successors'][1]]['live_in']
            keep_stream = not self.lookup_dead_outputs or stream_name in after
            keep_position = not self.lookup_dead_outputs or position_name in after
            stream = self.variable(frame, stream_name) if keep_stream else None
            position = self.variable(frame, position_name) if keep_position else None
            result = self.variable(frame, result_name)
            e = self.variable(frame, program)
            A, B, Q, R, C = self.micro
            code += [self.copy(C, result), self.copy(A, e), self.move(B, old_address)]
            self.free(frame, old_address)
            inner = self.fresh('lookup_record')
            code += [self.while_decnz(B, [self.clear(C),
                self.label(inner, [self.half_kernel(), self.move(A, Q),
                    [R.decnz, [C.inc, 'continue_'+inner]]])])]
            code += [self.clear(stream), self.move(stream, A)] if keep_stream else [self.clear(A)]
            if keep_position:
                code += [self.clear(position)]
            code += [self.clear(result), self.move(result, C)]
            self.lookup_certificate.append(dict(function=frame['name'],
                line=statements[index].lineno, program=program,
                address=ast.unparse(address), stream=stream_name,
                position=position_name, result=result_name,
                live_after=after, stream_output_kept=keep_stream, position_output_kept=keep_position,
                boundary='all source outputs restored; zero address preserves old result',
                scratch='A stream, B record countdown, C decoded count; half changes only A/Q/R',
                event_free=True))
            index += 2
        return code
