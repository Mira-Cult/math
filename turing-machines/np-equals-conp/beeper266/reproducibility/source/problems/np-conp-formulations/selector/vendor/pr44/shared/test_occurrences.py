"""Literal backend validation at every unfolded occurrence of a finite grammar.

Independently computes binary-path return/continue semantics and compares each
actual emitted transition sequence with its unbounded register representation.
Finite test values support the separate general proof; they do not replace it.
"""
from collections import Counter
import argparse
import json
from pathlib import Path
import sys


def paths(builder):
    def visit(index, path):
        sequence = builder.sequences[index]
        assert len(sequence.seq) == 2
        for choice, child in enumerate(sequence.seq):
            extended = path + (choice,)
            if type(child) is int:
                yield from visit(child, extended)
            else:
                yield extended, child, sequence.name
    yield from visit(builder.find_seq('main().0'), (1, 1, 0))


def return_path(path, skips):
    for position in range(len(path) - 1, 1, -1):
        if path[position] == 0:
            if skips:
                skips -= 1
            else:
                return path[:position] + (1,)
    raise AssertionError(('return outside root', path, skips))


def continue_path(path, skips):
    for position in range(len(path) - 1, 0, -1):
        if path[position] == 1:
            if skips:
                skips -= 1
            else:
                return path[:position + 1]
    raise AssertionError(('continue outside root', path, skips))


def encode(path, anchor, registers):
    cells = {position for position, bit in enumerate(path) if bit}
    cells.add(anchor)
    cursor = anchor + 2
    for value in registers:
        cells.update(range(cursor, cursor + value + 1))
        cursor += value + 2
    return cells


def check(builder, max_steps=200000):
    # All inputs are produced by independently specified representation rules.
    # No production arithmetic, tape decoder, or lexical transfer helper used.
    table = {(state, int(read)): (int(row.write), 1 if row.direction == 'R' else -1, row.nextstate)
             for (state, read), row in builder.tm.states.items()}
    occurrences = tuple(paths(builder))
    anchor = max(len(path) for path, leaf, parent in occurrences) + 5
    registers = tuple(builder.registers)
    indices = {name: index for index, name in enumerate(registers)}
    counts = Counter()
    for serial, (path, leaf, parent) in enumerate(occurrences):
        op = str(leaf)
        primitive = op == 'beep' or op.startswith('3.')
        cases = (0, 1) if op.endswith('.decnz') else (0,)
        for nonzero in cases:
            values = [(index + serial) % 3 for index in range(len(registers))]
            expected_values = values.copy()
            if op == 'beep':
                expected_path = return_path(path, 0)
                kind = 'beep'
            elif op.startswith('3.'):
                register, kind = op[2:].rsplit('.', 1)
                index = indices[register]
                if kind == 'inc':
                    expected_values[index] += 1
                    expected_path = return_path(path, 0)
                else:
                    assert kind == 'decnz'
                    values[index] = nonzero
                    expected_values[index] = 0
                    expected_path = return_path(path, int(nonzero == 0))
            elif op.startswith('_break.'):
                kind = 'break'
                expected_path = return_path(path, int(op.split('.')[1]))
            else:
                assert op.startswith('_continue.')
                kind = 'continue'
                expected_path = continue_path(path, int(op.split('.')[1]))
            tape = encode(path, anchor, values)
            state = op if primitive else parent
            head = len(path) if primitive else len(path) - 1
            beeps = 0
            for used in range(max_steps):
                if state == '4.dispatch.scan' and head < 0 and not any(
                        index in tape for index in range(max(len(path), len(expected_path)), anchor)):
                    break
                write, direction, target = table[state, int(head in tape)]
                beeps += state == 'B'
                if write:
                    tape.add(head)
                else:
                    tape.discard(head)
                head += direction
                state = target
            else:
                raise AssertionError(('literal occurrence fuel', serial, path, op))
            expected_tape = encode(expected_path, anchor, expected_values)
            # The proven engine permits only finitely many extra zero registers.
            tail = anchor + 2 + sum(value + 2 for value in expected_values)
            while tail in tape:
                expected_tape.add(tail)
                tail += 2
            assert tape == expected_tape, ('literal occurrence tape', serial, op, path,
                                            sorted(tape ^ expected_tape))
            assert beeps == int(op == 'beep'), ('literal occurrence beep count', serial, op, beeps)
            counts[kind] += 1
            counts['physical_transitions'] += used
    return {'occurrences': len(occurrences), 'cases': sum(counts[kind] for kind in ('beep','inc','decnz','break','continue')),
            'counts': dict(counts)}


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--code', type=Path, required=True)
    parser.add_argument('--source', type=Path)
    args = parser.parse_args()
    sys.path.insert(0, str(args.code.resolve()))
    from natural import NaturalBuilder
    from backend import add_literal_initializer, totalize_silently
    source = args.source or args.code / 'source.py'
    builder = NaturalBuilder(source.read_text()).build_machine()
    add_literal_initializer(builder)
    totalize_silently(builder)
    builder.tm.gc()
    print(json.dumps({'status': 'passed', **check(builder)}, sort_keys=True, indent=2))


if __name__ == '__main__':
    main()
