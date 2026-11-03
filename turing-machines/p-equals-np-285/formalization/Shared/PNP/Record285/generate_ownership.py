#!/usr/bin/env python3
"""Extract untrusted ownership graph, masks and coalescing certificate.

The inputs are byte-frozen producer packets. Lean checks every generated
invariant and graph relation independently of this generator.
"""
from collections import deque
from hashlib import sha256
from pathlib import Path
import argparse
import json
import re

HERE = Path(__file__).resolve().parent
parser = argparse.ArgumentParser()
parser.add_argument('--check', action='store_true')
args = parser.parse_args()

def load(name, expected):
    raw = (HERE / name).read_bytes()
    if sha256(raw).hexdigest() != expected:
        raise ValueError(f'unexpected input bytes: {name}')
    return json.loads(raw)

invariant = load('producer-coalescence-invariant.json',
                 'f18a1ad1b495f22fa5e8022cdec487c21690ea0c700a64e687f13d6d6221e878')
coalescence = load('producer-bank-coalescence.json',
                   'c9814aac0147541817b7b1abe2f716b77d02950a3f6bd73e2dba3e1003ed1d65')
late = load('producer-late-zero.json',
            '0c52735985fa5ab3148140805879ad0066a5d168560fa9438f428149475960ea')
logical_names = invariant['register_order']
name_index = {name: i for i, name in enumerate(logical_names)}
classes = [int(coalescence['mapping'][name].split('.')[-1]) for name in logical_names]
if len(classes) != 18 or set(classes) != set(range(15)):
    raise ValueError('unexpected logical-to-physical class mapping')
moves = {op['name']: op for op in invariant['operations']}
logical_rows = invariant['core_graph']['rows']
physical_rows = late['input_core_graph']['rows']
masks = invariant['states_at_core_rows']
if len(logical_rows) != 151 or len(masks) != len(logical_rows):
    raise ValueError('unexpected ownership graph dimensions')

def parse_action(op):
    if op == 'beep': return ('beep',)
    if op in moves:
        move = moves[op]
        return ('move', name_index[move['source']], name_index[move['destination']])
    half = re.fullmatch(r'3\.\$native-half:(.+)\.decnz', op)
    if half: return ('half', name_index[half[1]])
    ordinary = re.fullmatch(r'3\.(.+)\.(inc|decnz)', op)
    if ordinary:
        return ('inc' if ordinary[2] == 'inc' else 'dec', name_index[ordinary[1]])
    raise ValueError(f'unexpected action: {op}')

def physical_action(action):
    if action[0] == 'beep': return 'beep'
    kind, i = action[:2]
    if kind == 'half': return f'3.$native-half:$coalesced.{classes[i]}.decnz'
    if kind in ('dec', 'move'): return f'3.$coalesced.{classes[i]}.decnz'
    return f'3.$coalesced.{classes[i]}.inc'

mapping, reverse = {}, {}
todo = deque([(invariant['core_graph']['entry'], late['input_core_graph']['entry'])])
while todo:
    old, new = todo.popleft()
    if old in mapping:
        if mapping[old] != new: raise ValueError('nonfunctional row mapping')
        continue
    if new in reverse: raise ValueError('duplicate logical occurrence')
    mapping[old], reverse[new] = new, old
    row, target = logical_rows[old], physical_rows[new]
    action = parse_action(row[0])
    if target[0] != physical_action(action):
        raise ValueError(f'operation mismatch at logical row {old}')
    if action[0] == 'move':
        src, dst = action[1:]
        if classes[src] == classes[dst] or len(row) != 2 or len(target) != 3:
            raise ValueError('bad ownership move')
        body = physical_rows[target[1]]
        if body != [f'3.$coalesced.{classes[dst]}.inc', new]:
            raise ValueError('move loop does not return to its test')
        todo.append((row[1], target[2]))
    else:
        if len(row) != len(target): raise ValueError('branch count differs')
        todo.extend(zip(row[1:], target[1:]))
if set(mapping) != set(range(len(logical_rows))):
    raise ValueError('unmapped logical graph row')

def lean_action(op):
    action = parse_action(op)
    return '.' + action[0] + ''.join(' ' + str(i) for i in action[1:])

out = ['import Shared.PNP.Record285.OwnershipCore', '',
       '/-! Generated ownership rows, masks and class/graph maps. -/',
       'namespace Shared.PNP.Record285.OwnershipCore', '',
       'def logicalRows : Array Row := #[']
for i, row in enumerate(logical_rows):
    yes = row[2] if len(row) == 3 else row[1]
    out.append(f'  ⟨{lean_action(row[0])},{row[1]},{yes}⟩' + (',' if i+1 < len(logical_rows) else ''))
out += [']', '', 'def logicalMasks : Array (Array Nat) := #[']
for i, mask in enumerate(masks):
    if mask is None or len(mask) != 18 or any(c not in '1234567' for c in mask):
        raise ValueError(f'invalid logical mask at {i}')
    out.append('  #[' + ','.join(mask) + ']' + (',' if i+1 < len(masks) else ''))
out += [']', '', 'def classMap : Array Nat := #[' + ','.join(map(str, classes)) + ']',
        '', 'def graphMap : Array Nat := #[' + ','.join(str(mapping[i]) for i in range(len(logical_rows))) + ']',
        '', 'end Shared.PNP.Record285.OwnershipCore', '']
generated = '\n'.join(out)
path = HERE / 'OwnershipData.lean'
if args.check:
    if path.read_text() != generated: raise ValueError('generated ownership data differs')
else:
    path.write_text(generated)
print(f'{len(logical_rows)} logical rows; {len(physical_rows)} physical rows; {len(moves)} move templates')
