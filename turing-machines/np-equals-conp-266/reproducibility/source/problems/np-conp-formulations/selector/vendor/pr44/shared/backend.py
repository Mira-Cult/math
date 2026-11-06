"""Small explicit adapters for the pinned Wade/TMBuilder binary engine.

This is new Research Order 15 code. It does not modify the inspected repositories.
Call after b.main(); b.reduce_to_cons(); b.name_sequences(); b.generate().
The caller may factor the grammar before reduce_to_cons. Call gc after adapters.
"""
from collections import Counter


def leaf_paths(builder):
    """Occurrences, not shared nodes: yield (path, instruction)."""
    root = builder.find_seq('main().0')
    def walk(item, path):
        if isinstance(item, int):
            seq = builder.sequences[item].seq
            assert len(seq) == 2
            yield from walk(seq[0], path + '0')
            yield from walk(seq[1], path + '1')
        else:
            yield path, str(item)
    yield from walk(root, '110')


def add_beep(builder):
    """One exit from B per completed beep primitive, including preparation."""
    import tm
    rows = builder.tm.states
    rows['beep', '0'] = tm.Transition('1', 'R', '1b.reg.prep_1')
    rows['beep', '1'] = tm.Transition('0', 'L', 'B')
    # A clone of one step, NOT a B self-loop on carry.
    rows['B', '0'] = tm.Transition('1', 'R', '2e.reg.cleanup_1')
    rows['B', '1'] = tm.Transition('0', 'L', '6.break.0')


def add_literal_initializer(builder, padding=None):
    """Counted blank initializer to a source-entry configuration.

    All N source registers are zero. P is the bank-anchor position. The two
    adjacent ones at 0,1 are the unique 11 in this initialized tape, permitting
    the 4-state return scanner. Every emitted transition is binary and L/R.
    """
    import tm
    paths = list(leaf_paths(builder))
    max_path = max(len(p) for p, _ in paths)
    P = max_path + 3 if padding is None else padding
    assert P >= max_path + 2
    N = len(builder.registers)
    assert N >= 1
    ones = {0, 1} | {P + 2*i for i in range(N+1)}
    length = P + 2*N + 2
    rows = builder.tm.states
    for i in range(length):
        bit = str(int(i in ones))
        direction = 'R' if i + 1 < length else 'L'
        target = f'init.{i+1}' if i + 1 < length else 'init.scan'
        for read in '01':
            rows[f'init.{i}', read] = tm.Transition(bit, direction, target)
    rows['init.scan', '0'] = tm.Transition('0', 'L', 'init.scan')
    rows['init.scan', '1'] = tm.Transition('1', 'L', 'init.previous')
    rows['init.previous', '0'] = tm.Transition('0', 'L', 'init.scan')
    rows['init.previous', '1'] = tm.Transition('1', 'R', 'init.right1')
    for read in '01':
        rows['init.right1', read] = tm.Transition(read, 'R', 'init.right2')
        rows['init.right2', read] = tm.Transition(read, 'R', 'main().0')
    builder.tm.start = builder.tm.statename = 'init.0'
    return dict(padding=P, registers=N, max_leaf_path=max_path,
                initializer_states=length+4, entry='main().0', head=3,
                ones=sorted(ones))


def totalize_silently(builder):
    """Missing rows enter a counted silent sink; valid runs avoid every repair."""
    import tm
    rows = builder.tm.states
    states = {q for q, _ in rows} | {t.nextstate for t in rows.values()}
    missing = [(q, b) for q in states for b in '01' if (q, b) not in rows]
    for q, b in missing:
        rows[q, b] = tm.Transition(b, 'R', 'silent.sink')
    if missing:
        for b in '01':
            rows['silent.sink', b] = tm.Transition(b, 'R', 'silent.sink')
    builder.tm.symbols = {'0', '1'}
    return missing
