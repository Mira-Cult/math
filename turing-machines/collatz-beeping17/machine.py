#!/usr/bin/env python3
"""17-state, two-symbol blank-tape beeping machine for full positive Collatz.

Run: python3 machine.py
Emit the compact table: python3 machine.py --emit
See README.md for the all-input argument; finite tests are not that proof.
Arithmetic geometry adapted from calr3/tinycryptids weakcollatz-14,
commit ad9c597ad728f301400325b8e2115a4bb62a25d3.
"""
from __future__ import annotations
import argparse
from pathlib import Path

# Each entry is (write, direction, target), encoded as a readable string.
# The first eleven states implement unbounded shortcut-Collatz iteration.
# The last six implement a reusable unary counter increment + hole-position copy.
NAMED: dict[str, tuple[str, str]] = {
    'disp': ('1RputHole', '0RtoH'),
    'toH': ('1LstepH', '1RtoH'),
    'stepH': ('0Lhome', '0Lback'),
    'back': ('1Rmark', '1Lback'),
    'mark': ('0Rhop2', '0RtoH'),
    'hop2': ('0LbackO', '0LbackO'),
    'backO': ('1LmarkO', '1LbackO'),
    'markO': ('0Rdisp', '0RtoHO'),
    'toHO': ('1Rhop1', '1RtoHO'),
    'hop1': ('1Rhop2', '1Rhop2'),
    'home': ('0Rdisp', '1Lhome'),
    'putHole': ('0LbackOutput', '0LbackOutput'),
    'backOutput': ('0LbackCounter', '1LbackOutput'),
    'backCounter': ('1RcopyMark', '1LbackCounter'),
    'copyMark': ('0Rdisp', '0RskipCounter'),
    'skipCounter': ('0Rworkscan', '1RskipCounter'),
    'workscan': ('1RputHole', '1Rworkscan'),
}
NAMES = tuple(NAMED)
LETTERS = {name: chr(65+i) for i, name in enumerate(NAMES)}
START = 'disp'
BEEP = 'copyMark'  # O. Beep on every exit, irrespective of the read symbol.
TABLE = {
    name: tuple((int(t[0]), 1 if t[1] == 'R' else -1, t[2:]) for t in row)
    for name, row in NAMED.items()
}
COMPACT = '_'.join(''.join(t[:2]+LETTERS[t[2:]] for t in row)
                   for row in NAMED.values())
PINNED = ('1RL0RB_1LC1RB_0LK0LD_1RE1LD_0RF0RB_0LG0LG_1LH1LG_'
          '0RA0RI_1RJ1RI_1RF1RF_0RA1LK_0LM0LM_0LN1LM_1RO1LN_'
          '0RA0RP_0RQ1RP_1RL1RQ')


def require(condition: bool, message: object) -> None:
    """Checks remain enabled under python -O."""
    if not condition:
        raise AssertionError(message)


def configuration(n: int, v: int, capacity: int) -> set[int]:
    """C(n,v,K): head at cell 0 in A, separator at -1."""
    if not (n >= 1 and 1 <= v <= capacity):
        raise ValueError('require n >= 1 and 1 <= v <= capacity')
    return set(range(-n, -1)) | (set(range(capacity)) - {v-1})


def step(tape: set[int], head: int, state: str) -> tuple[int, str]:
    write, direction, target = TABLE[state][int(head in tape)]
    if write:
        tape.add(head)
    else:
        tape.discard(head)
    return head + direction, target


def shortcut(v: int) -> int:
    if v < 1:
        raise ValueError('positive values only')
    return v // 2 if v % 2 == 0 else (3*v+1) // 2


def macro(n: int, v: int, capacity: int,
          limit: int = 10_000_000) -> tuple[set[int], int, int, int]:
    tape = configuration(n, v, capacity)
    head, state, beeps = 0, START, 0
    for time in range(1, limit+1):
        beeps += state == BEEP
        head, state = step(tape, head, state)
        if state == START:
            return tape, head, time, beeps
    raise TimeoutError((n, v, capacity, head, state))


def expected(n: int, v: int, capacity: int) -> tuple[set[int], int]:
    if v == 1:
        return configuration(n+1, n+1, max(capacity, n+1)), n
    value = shortcut(v)
    return configuration(n, value, max(capacity, value)), 0


def verify() -> None:
    require(len(TABLE) == 17, 'state count')
    require(COMPACT == PINNED, 'compact table mismatch')
    require(LETTERS[BEEP] == 'O', 'beep state')
    for row in TABLE.values():
        for w, d, target in row:
            require(w in (0, 1) and d in (-1, 1) and target in TABLE, 'transition')
    cases = 0
    for n in range(1, 8):
        for v in range(1, 61):
            for capacity in sorted({v, v+1, v+2, v+7, 2*v}):
                tape, head, _, beeps = macro(n, v, capacity)
                want, want_beeps = expected(n, v, capacity)
                require(head == 0 and tape == want and beeps == want_beeps,
                        (n, v, capacity, head, beeps))
                cases += 1
    print(f'PASS: {cases} macro cases; 17 states; beep state O')


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--emit', action='store_true', help='print compact table')
    args = parser.parse_args()
    if args.emit:
        print(COMPACT)
    else:
        verify()
