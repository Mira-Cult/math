#!/usr/bin/env python3
"""Independent literal-table regression for the 17-state Collatz beeper.

No imports from machine.py or validate.cpp. Checks first-return configuration,
beeps, exact macro lengths, and exact visited-cell intervals. Finite tests do
not prove the all-input theorem. Run from this directory: python3 independent_check.py
"""
import hashlib
import json
import random
import re
from pathlib import Path

TABLE_PATH = Path(__file__).parent / 'collatz_beeping17.tm'
raw = TABLE_PATH.read_bytes()
text = raw.decode().strip()
if not re.fullmatch(r'[01][LR][A-Q][01][LR][A-Q](?:_[01][LR][A-Q][01][LR][A-Q]){16}', text):
    raise RuntimeError('invalid literal 17-state table')
table = [[(int(row[i]), -1 if row[i+1] == 'L' else 1, ord(row[i+2])-65)
          for i in (0, 3)] for row in text.split('_')]

def tape_for(n, v, k):
    return set(range(-n, -1)) | (set(range(k)) - {v - 1})

def test(n, v, k):
    if not (n >= 1 and 1 <= v <= k):
        raise ValueError((n, v, k))
    if v == 1:
        nn, vv, beeps_expected = n + 1, n + 1, n
        length_expected = 2 * n * (n + 2)
        lo_expected, hi_expected = -n - 1, n
    elif v % 2 == 0:
        nn, vv, beeps_expected = n, v // 2, 0
        length_expected = 2 * vv * (vv + 1)
        lo_expected, hi_expected = -1, v - 1
    else:
        half = (v - 1) // 2
        nn, vv, beeps_expected = n, 3 * half + 2, 0
        length_expected = 5 * half * half + 9 * half + 4
        lo_expected, hi_expected = -1, vv - 1
    expected_tape = tape_for(nn, vv, max(k, vv))
    tape = tape_for(n, v, k)
    pos = state = beeps = 0
    lo = hi = 0
    for time in range(1, length_expected + 1):
        if state == 14:
            beeps += 1
        w, delta, state = table[state][int(pos in tape)]
        if w:
            tape.add(pos)
        else:
            tape.discard(pos)
        pos += delta
        lo = min(lo, pos)
        hi = max(hi, pos)
        if state == 0:
            if not (time == length_expected and pos == 0 and tape == expected_tape
                    and beeps == beeps_expected
                    and (lo, hi) == (lo_expected, hi_expected)):
                raise AssertionError((n, v, k, time, length_expected, pos, beeps, lo, hi))
            return time
    raise AssertionError(('no expected first return', n, v, k, pos, state))

def main():
    cases = []
    # Every positive v through 64 at five independently selected counter sizes,
    # with boundary holes and substantial untouched trailing capacity.
    for n in (1, 2, 3, 7, 17):
        for v in range(1, 65):
            for k in sorted({v, v + 1, v + 5, 257}):
                cases.append((n, v, k))
    # More counter sizes and very long untouched tails for reset/copy.
    for n in range(1, 129):
        for k in sorted({1, n + 1, 4096}):
            cases.append((n, 1, k))
    # Boundary and larger arithmetic cases; randomness is reproducible.
    rng = random.Random(0xC011A72)
    for _ in range(128):
        n, v = rng.randrange(1, 513), rng.randrange(1, 1001)
        cases.append((n, v, v + rng.randrange(4097)))
    for n in (1, 2, 255, 256, 257, 1024):
        cases.append((n, 1, 10000))
    for v in (127, 128, 129, 255, 256, 257, 999, 1000, 1001):
        cases.append((1024, v, 10000))
    steps = sum(test(*c) for c in cases)
    print(json.dumps({
        'status': 'PASS', 'cases': len(cases), 'transitions': steps,
        'table_sha256': hashlib.sha256(raw).hexdigest(),
        'checks': ['first return to A', 'head at zero', 'entire tape',
                   'exact beep count', 'exact macro length', 'exact visited interval'],
        'length_formulas': {'v=1': '2*n*(n+2)', 'v=2*k': '2*k*(k+1)',
                            'v=2*k+1, k>=1': '5*k*k+9*k+4'},
    }, indent=2))

if __name__ == '__main__':
    main()
