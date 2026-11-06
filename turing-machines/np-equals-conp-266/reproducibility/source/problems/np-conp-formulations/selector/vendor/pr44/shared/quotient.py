"""Exact beep-colored deterministic transition quotient and certificate check."""
from machine import Machine


def check_quotient(old, new, mapping):
    assert set(mapping) == set(range(old.count))
    assert set(mapping.values()) == set(range(new.count))
    assert mapping[old.start] == new.start
    assert mapping[old.beep] == new.beep
    for q in range(old.count):
        assert (q == old.beep) == (mapping[q] == new.beep)
        for b in (0, 1):
            w, d, target = old.rows[q, b]
            assert new.rows[mapping[q], b] == (w, d, mapping[target])


def quotient(old):
    colors = [int(q == old.beep) for q in range(old.count)]
    while True:
        keys = [(q == old.beep, tuple((w, d, colors[t])
                for w, d, t in (old.rows[q, 0], old.rows[q, 1])))
                for q in range(old.count)]
        partition = {}
        refined = [partition.setdefault(key, len(partition)) for key in keys]
        if len(set(refined)) == len(set(colors)):
            colors = refined
            break
        colors = refined
    order = list(dict.fromkeys([colors[old.start], colors[old.beep]]))
    order += sorted(set(colors) - set(order))
    rename = {c: i for i, c in enumerate(order)}
    mapping = {q: rename[colors[q]] for q in range(old.count)}
    rows = {(mapping[q], b): (w, d, mapping[t])
            for (q, b), (w, d, t) in old.rows.items()}
    new = Machine(mapping[old.start], mapping[old.beep], rows)
    check_quotient(old, new, mapping)
    return new, mapping
