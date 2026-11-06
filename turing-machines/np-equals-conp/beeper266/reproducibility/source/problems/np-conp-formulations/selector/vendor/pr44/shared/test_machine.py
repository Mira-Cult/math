"""Independent table parsing and source/register/literal-tape correspondence."""
import json
from pathlib import Path
import tempfile

from natural import NaturalBuilder
from backend import add_literal_initializer, totalize_silently
from build import canonicalize
from machine import emit, parse, simulate
from test_natural import TreeVM


def decode_registers(tape, anchor, names):
    ones = set(tape)
    assert anchor in ones and anchor + 1 not in ones
    cursor = anchor + 2
    registers = {}
    for name in names:
        length = 0
        while cursor in ones:
            length += 1
            cursor += 1
        assert length > 0
        registers[name] = length - 1
        cursor += 1
    return registers


def compiled(source, entry='main', args=()):
    b = NaturalBuilder(source, entry, args).build_machine()
    spec = add_literal_initializer(b)
    totalize_silently(b)
    b.tm.gc()
    m, mapping = canonicalize(b)
    return b, spec, m


def compare_events(source, expected_events, entry='main', args=(), limit=20000000):
    b, spec, machine = compiled(source, entry, args)
    vm = TreeVM(b)
    # This interpreter is separately written and follows register/path semantics.
    while len(vm.beep_records) < expected_events:
        vm.step()
        assert vm.steps < 200000
    current = None
    physical_times = []
    total_steps = 0
    for source_step, expected_regs in vm.beep_records:
        trace = simulate(machine, limit, initial=current, stop_after_beeps=1)
        assert len(trace['beeps']) == 1, ('no beep within finite test allowance', trace['steps'])
        actual = decode_registers(trace['ones'], spec['padding'], b.registers)
        for name in b.registers:
            assert actual[name] == expected_regs.get(name, 0), (name, actual[name], expected_regs.get(name, 0))
        total_steps += trace['steps']
        physical_times.append(total_steps)
        current = (trace['state'], trace['head'], trace['ones'])
    return total_steps, physical_times


def main():
    invalid = [-1, 1.5, '2']
    for value in invalid:
        try:
            NaturalBuilder('def f(a):\n    return a\n', 'f', (value,))
        except ValueError:
            pass
        else:
            raise AssertionError('invalid entry argument accepted')
    # Main's real source is nontrivial; unsupported degenerate root is an API
    # limitation, not part of its compiler theorem.
    arithmetic = 'def f(a,b):\n    return a+b,a-b,a*b,a//b,a%b,a**b,a<b,a==b\n'
    cases = [compare_events(arithmetic, 1, 'f', args) for args in ((0, 0), (2, 3), (3, 2))]
    template = '''def main():
    j, i = 0, 0
    beep()
    while True:
        if j == CORRECT:
            i += 1
        else:
            if i == j:
                beep()
                j += 1
                i = 0
            else:
                i += 1
'''
    cases += [compare_events(template.replace('CORRECT', '0'), 1),
              compare_events(template.replace('CORRECT', '3'), 4),
              compare_events(template.replace('j == CORRECT', 'False'), 6)]
    with tempfile.TemporaryDirectory() as tmp:
        _, _, m = compiled('def main():\n    while True:\n        beep()\n')
        path = Path(tmp) / 'm.tm'
        emit(m, path)
        assert parse(path).rows == m.rows
        text = path.read_text()
        rows = text.splitlines()
        mutations = [text + rows[-1] + '\n', '\n'.join(rows[:-1]) + '\n',
                     text.replace(' R ', ' S ', 1), text.replace('#! blank 0', '#! blank 1'),
                     text.replace('#! states ', '#! nonsense ', 1),
                     text.replace('#! beep 1', '#! beep 999999')]
        for mutated in mutations:
            path.write_text(mutated)
            try:
                parse(path)
            except ValueError:
                pass
            else:
                raise AssertionError('corrupt table accepted')
    print(json.dumps(dict(status='pass', physical_trace_fixtures=len(cases),
                         physical_steps=sum(s for s, _ in cases),
                         event_times=[t for _, t in cases], parser_negative_cases=len(mutations))))


if __name__ == '__main__':
    main()
