"""Finite certificates for unreachable TM inputs, without bounded execution.

A certificate is a finite set of abstract configurations (q, local word,
incoming direction), containing the initial all-zero window and closed under
BOTH possible newly exposed boundary bits. Therefore it covers every step
of the concrete infinite-tape computation, for arbitrarily large time.
"""
from collections import deque


def build_certificate(machine, radius=1, start=0):
    if radius < 0:
        raise ValueError('Radius must be nonnegative')
    width = 2 * radius + 1
    mask = (1 << width) - 1
    seen = {(start, 0, 'start')}
    queue = deque(seen)
    while queue:
        q, word, _ = queue.popleft()
        a = (word >> radius) & 1
        if (q, a) not in machine:
            continue
        target, b, direction = machine[q, a]
        written = (word & ~(1 << radius)) | (b << radius)
        for bit in (0, 1):
            shifted = ((written >> 1) | (bit << (width - 1)) if direction == 'R'
                       else ((written << 1) & mask) | bit)
            successor = target, shifted, direction
            if successor not in seen:
                seen.add(successor)
                queue.append(successor)
    return {'radius': radius, 'start_state': start, 'blank': 0,
            'states': [list(s) for s in sorted(seen)]}


def check_certificate(machine, certificate, *, expected_start=0):
    """Check closure independently, using explicit word lists, not bit shifts."""
    radius = certificate['radius']
    if not isinstance(radius, int) or radius < 0 or certificate['blank'] != 0:
        raise ValueError('Invalid window parameters')
    width = 2 * radius + 1
    states = {tuple(s) for s in certificate['states']}
    start = certificate['start_state']
    if start != expected_start:
        raise ValueError('Certificate uses a different initial state')
    if (start, 0, 'start') not in states:
        raise ValueError('The blank initial configuration is missing')
    for q, word, incoming in states:
        if not isinstance(word, int) or not 0 <= word < 2 ** width:
            raise ValueError('Invalid window word')
        if incoming not in ('start', 'L', 'R'):
            raise ValueError('Invalid incoming direction')
        cells = [(word // (2 ** i)) % 2 for i in range(width)]
        transition = machine.get((q, cells[radius]))
        if transition is None:
            continue
        target, written, direction = transition
        cells[radius] = written
        for exposed in (0, 1):
            next_cells = cells[1:] + [exposed] if direction == 'R' else [exposed] + cells[:-1]
            next_word = sum(value * (2 ** i) for i, value in enumerate(next_cells))
            if (target, next_word, direction) not in states:
                raise ValueError(f'Certificate not closed at {(q, word, incoming)}')
    return True


def allowed_inputs(certificate):
    radius = certificate['radius']
    return {(q, direction, (word >> radius) & 1)
            for q, word, direction in certificate['states'] if direction in ('L', 'R')}
