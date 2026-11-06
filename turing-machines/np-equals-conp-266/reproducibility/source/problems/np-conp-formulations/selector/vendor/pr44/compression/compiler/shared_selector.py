"""Share the INC/DECNZ bank selector under an explicit physical domain.

The input must be the unchanged pinned TMBuilder runtime after complete source
compilation. This is a representation change, not all-configuration equivalence.
See SHARED_SELECTOR.md. The small bootstrap keeps its old register-zero ABI.
"""
from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parents[2]
sys.path[:0] = [str(ROOT / 'shared'), str(ROOT / 'shared/vendor')]
import tm
from TMBuilder import framework
from backend import leaf_paths, totalize_silently

PREFIX = 'shared.selector.'


def row_tuple(row):
    return row.write, row.direction, row.nextstate


def check_input(builder):
    rows = builder.tm.states
    if any(q.startswith(PREFIX) for q, _ in rows):
        raise ValueError('selector namespace already used')
    registers = tuple(builder.registers.values())
    if not registers or len(registers) > 1909:
        raise ValueError('compact bootstrap register bound')
    paths = tuple(leaf_paths(builder))
    if not paths or max(len(p) for p, _ in paths) >= 3822:
        raise ValueError('compact bootstrap gap must admit the extra separator')
    depth = max(p.count('0') for p, _ in paths) + 1
    zero = registers[0]
    def expect(q, read, write, direction, target):
        actual = rows.get((q, read))
        if actual is None or row_tuple(actual) != (write, direction, target):
            raise ValueError('unexpected runtime row: ' + repr((q, read)))
    # Validate the whole inherited runtime, not just the rows overwritten below.
    substitutions = {'[3.register_0.inc]': zero.inc,
                     '[3.register_0.decnz]': zero.decnz,
                     '[largest_4.dispatch]': f'4.dispatch.{depth}'}
    for line in framework.splitlines():
        fields = line.split()
        if not fields or fields[0].startswith('#'):
            continue
        q, read, write, direction, target = fields
        expect(q, read, write, direction, substitutions.get(target, target))
    for i in range(1, depth + 1):
        expect(f'4.dispatch.{i}', '0', '0', 'L', f'4.dispatch.{i-1}')
        expect(f'4.dispatch.{i}', '1', '1', 'L', f'4.dispatch.{i}')
    extra = {q for q, _ in rows if q.startswith('4.dispatch.') and q.rsplit('.', 1)[1].isdigit()}
    if extra != {f'4.dispatch.{i}' for i in range(depth + 1)}:
        raise ValueError('unexpected dispatcher inventory')
    for i, reg in enumerate(registers):
        for op, terminal in (('inc', reg.inc), ('dec', reg.decnz)):
            expect(terminal, '0', '1', 'R', '1b.reg.prep_1')
            expect(terminal, '1', '0', 'R', f'2b.reg.{i}.{op}')
            expect(f'2b.reg.{i}.{op}', '0', '0', 'R', f'2b.reg.{i-1}.{op}')
            expect(f'2b.reg.{i}.{op}', '1', '1', 'R', f'2b.reg.{i}.{op}')
    if builder.tm.start != '0a.boot1.A':
        raise ValueError('this recipe binds the inherited blank bootstrap')
    return registers, depth, paths


def apply(builder):
    """Mutate one freshly built machine, then totalize and collect dead rows.

    Source grammar and register order are unchanged. Ordinary invocation has
    clean gap P >= |path|+3. The separately preserved bootstrap supplies P=3824.
    """
    registers, depth, paths = check_input(builder)
    rows = builder.tm.states
    old = dict(rows)
    def put(q, read, write, direction, target):
        rows[q, str(read)] = tm.Transition(str(write), direction, target)
    def name(suffix):
        return PREFIX + suffix

    # The prepared phase now has two separator zeros, leaving h as the mode bit.
    put('1b.reg.prep_1', 0, 0, 'R', name('prep'))
    put(name('prep'), 0, 0, 'R', '1b.reg.prep_2')
    for index, reg in enumerate(registers):
        put(reg.inc, 1, 0, 'R', name(f'select.{index+1}'))
        put(reg.decnz, 1, 1, 'R', name(f'select.{index+1}'))
    for index in range(-1, len(registers)+1):
        q = name(f'select.{index}')
        successor = name(f'select.{index-1}') if index > -1 else name('mark')
        put(q, 0, 0, 'R', successor)
        put(q, 1, 1, 'R', q)
    # A selected block is nonempty. Its erased first one identifies it on return.
    put(name('mark'), 1, 0, 'L', name('skip_separator'))
    put(name('skip_separator'), 0, 0, 'L', name('left'))
    put(name('left'), 1, 1, 'L', name('left'))
    put(name('left'), 0, 0, 'L', name('left_zero'))
    put(name('left_zero'), 1, 1, 'L', name('left'))
    put(name('left_zero'), 0, 0, 'L', name('mode'))
    for mode in (0, 1):
        p = name(f'mode{mode}.')
        put(name('mode'), mode, 0, 'R', p+'pad1')
        put(p+'pad1', 0, 0, 'R', p+'pad2')
        put(p+'pad2', 0, 1, 'R', p+'right')
        put(p+'right', 1, 1, 'R', p+'right')
        put(p+'right', 0, 0, 'R', p+'right_zero')
        put(p+'right_zero', 1, 1, 'R', p+'right')
        put(p+'right_zero', 0, 1-mode, 'R',
            '2b.reg.-2.inc' if mode == 0 else '2b.reg.dec.check')
    # One additional prepared zero requires one additional counted dispatcher row.
    put(f'4.dispatch.{depth+1}', 0, 0, 'L', f'4.dispatch.{depth}')
    put(f'4.dispatch.{depth+1}', 1, 1, 'L', f'4.dispatch.{depth+1}')
    put('6.continue.0', 1, 1, 'L', f'4.dispatch.{depth+1}')

    # Boot2 is not an ordinary grammar call. Preserve its original short-gap ABI.
    zero = registers[0]
    for operation in ('inc', 'decnz'):
        original = getattr(zero, operation)
        alias = name('bootstrap.' + operation)
        for read in ('0', '1'):
            row = old[original, read]
            target = name('bootstrap.prep') if row.nextstate == '1b.reg.prep_1' else row.nextstate
            put(alias, read, row.write, row.direction, target)
        for q, read in (('0a.boot1.C', '1'), ('0b.boot2.2', '0'), ('0b.boot2.2', '1')):
            row = old[q, read]
            if row.nextstate == original:
                put(q, read, row.write, row.direction, alias)
    put(name('bootstrap.prep'), 0, 0, 'R', '1b.reg.prep_2')
    missing = totalize_silently(builder)
    builder.tm.gc()
    return {'kind': 'shared-selector-v1', 'registers': len(registers),
            'old_dispatch_depth': depth, 'new_dispatch_depth': depth+1,
            'max_leaf_path': max(len(path) for path, _ in paths),
            'ordinary_gap_slack': 3, 'bootstrap_adapter': 'preserved-register-zero',
            'event_scope': 'same source B-exit sequence; physical times may change',
            'domain': 'standard clean grammar occurrences and separately checked blank bootstrap',
            'new_totalized_rows': sorted(missing)}
