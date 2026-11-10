#!/usr/bin/env python3
"""Literal bounded interpreter; finite output cannot certify omega-acceptance."""
import argparse
import json
from pathlib import Path

parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument('--steps', type=int, default=100000, help='maximum executed transitions')
parser.add_argument('--table', type=Path, default=Path(__file__).with_name('machine.tm'))
args = parser.parse_args()
if args.steps < 0:
    parser.error('--steps must be nonnegative')
rows, headers = {}, {}
for line in args.table.read_text().splitlines():
    if line.startswith('#! '):
        key, value = line[3:].split(maxsplit=1)
        headers[key] = value
    else:
        q, read, write, direction, target, event = line.split()
        if (int(q),int(read)) in rows:
            raise ValueError('duplicate transition')
        if direction not in ('L','R') or write not in ('0','1') or event not in ('-','0','1'):
            raise ValueError('invalid transition')
        rows[int(q),int(read)] = int(write), (-1 if direction == 'L' else 1), int(target), event
n = int(headers['states'])
if headers['format'] != 'bit-events-v1' or headers['blank'] != '0':
    raise ValueError('unsupported format')
if set(rows) != {(q,b) for q in range(n) for b in range(2)} or any(not 0 <= r[2] < n for r in rows.values()):
    raise ValueError('not a complete nonhalting table')
state, head = int(headers['start']), int(headers['head'])
ones, events = set(), 0
for t in range(args.steps):
    before, read = state, int(head in ones)
    write, move, state, event = rows[state,read]
    if write:
        ones.add(head)
    else:
        ones.discard(head)
    head += move
    if event != '-':
        events += 1
        print(json.dumps({'transition_index':t,'state_before':before,'read':read,'output':int(event)}))
print(json.dumps({'executed_transitions':args.steps,'state':state,'head':head,'nonzero_cells':len(ones),'events':events}))
