"""Strict parser, structural validator, counter and independent literal simulator.

This module imports no compiler.  Time t=0 is the blank initial configuration.
Transition t+1 emits a beep iff its pre-transition state equals the header's B.
"""
from __future__ import annotations

import argparse
from dataclasses import dataclass
import hashlib
import json
from pathlib import Path


@dataclass
class Machine:
    start: int
    beep: int
    rows: dict

    @property
    def count(self):
        return len(self.rows) // 2


def parse(path):
    headers, rows = {}, {}
    for line_number, line in enumerate(Path(path).read_text().splitlines(), 1):
        if not line or line.startswith('# ') or line == '#':
            continue
        fields = line.split()
        if fields[0] == '#!':
            if len(fields) != 3 or fields[1] in headers:
                raise ValueError(('bad or duplicate header', line_number))
            headers[fields[1]] = fields[2]
            continue
        if len(fields) != 5:
            raise ValueError(('bad transition', line_number))
        q, bit, write, direction, target = fields
        if not all(x.isdecimal() and str(int(x)) == x for x in (q, target)):
            raise ValueError(('noncanonical state', line_number))
        if bit not in ('0', '1') or write not in ('0', '1') or direction not in ('L', 'R'):
            raise ValueError(('bad alphabet or move', line_number))
        key = int(q), int(bit)
        if key in rows:
            raise ValueError(('duplicate row', line_number))
        rows[key] = int(write), (-1 if direction == 'L' else 1), int(target)
    if set(headers) != {'format', 'states', 'start', 'beep', 'blank', 'head'}:
        raise ValueError('missing or unknown headers')
    if headers['format'] != 'beeper-v1' or headers['blank'] != '0' or headers['head'] != '0':
        raise ValueError('unsupported convention')
    for key in ('states', 'start', 'beep'):
        if not headers[key].isdecimal() or str(int(headers[key])) != headers[key]:
            raise ValueError('invalid numeric header')
    n, start, beep = (int(headers[x]) for x in ('states', 'start', 'beep'))
    if n < 1 or not 0 <= start < n or not 0 <= beep < n:
        raise ValueError('bad state count or distinguished state')
    if set(rows) != {(q, b) for q in range(n) for b in (0, 1)}:
        raise ValueError('table is not total with contiguous counted states')
    if any(not 0 <= t < n for w, d, t in rows.values()):
        raise ValueError('undefined successor')
    return Machine(start, beep, rows)


def emit(machine, path):
    lines = ['#! format beeper-v1', f'#! states {machine.count}',
             f'#! start {machine.start}', f'#! beep {machine.beep}',
             '#! blank 0', '#! head 0']
    for (q, b), (w, d, t) in sorted(machine.rows.items()):
        lines.append(f'{q} {b} {w} {"L" if d < 0 else "R"} {t}')
    Path(path).write_text('\n'.join(lines) + '\n')


def simulate(machine, transitions, *, stop_after_beeps=None, initial=None, stop_state=None):
    # Sparse support; every absent cell on the two-way infinite tape is zero.
    state, head, tape = (machine.start, 0, set()) if initial is None else initial
    tape = set(tape)
    times = []
    steps = 0
    while steps < transitions:
        if stop_state is not None and state == stop_state:
            break
        w, direction, target = machine.rows[state, int(head in tape)]
        if state == machine.beep:
            times.append(steps + 1)
        if w:
            tape.add(head)
        else:
            tape.discard(head)
        head += direction
        state = target
        steps += 1
        if stop_after_beeps is not None and len(times) >= stop_after_beeps:
            break
    return dict(steps=steps, state=state, head=head, ones=sorted(tape), beeps=times)


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('action', choices=('count', 'run'))
    ap.add_argument('table', type=Path)
    ap.add_argument('--steps', type=int, default=100000)
    ap.add_argument('--beeps', type=int)
    args = ap.parse_args()
    m = parse(args.table)
    if args.action == 'count':
        print(json.dumps(dict(states=m.count, transitions=len(m.rows), start=m.start,
                             B=m.beep, sha256=hashlib.sha256(args.table.read_bytes()).hexdigest()), indent=2))
    else:
        print(json.dumps(simulate(m, args.steps, stop_after_beeps=args.beeps)))


if __name__ == '__main__':
    main()
