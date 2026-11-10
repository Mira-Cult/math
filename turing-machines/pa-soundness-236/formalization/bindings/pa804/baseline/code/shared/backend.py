"""Totalization adapter extracted from the frozen backend, not a byte copy."""
def totalize_silently(builder):
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
