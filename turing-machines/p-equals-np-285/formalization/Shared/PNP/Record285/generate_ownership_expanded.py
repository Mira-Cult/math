#!/usr/bin/env python3
"""Extract the untrusted pre-contraction graph and occurrence mapping.

The Lean checker validates every retained row and each complete move loop.
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

packet = load('producer-ownership-contraction.json',
              '8bc8909289c572829cc27a92d3d48689a38ba813cd98faae2f45cfc1cc0eda13')
invariant = load('producer-coalescence-invariant.json',
                 'f18a1ad1b495f22fa5e8022cdec487c21690ea0c700a64e687f13d6d6221e878')
grammar = packet['before_grammar']
logical_rows = invariant['core_graph']['rows']
names = invariant['register_order']
index = {name: i for i, name in enumerate(names)}
moves = {op['name']: op for op in packet['operations']}

def parse(op):
    if op == 'beep': return ('beep',)
    if op in moves:
        move = moves[op]
        return ('move', index[move['source']], index[move['destination']])
    half = re.fullmatch(r'3\.\$native-half:(.+)\.decnz', op)
    if half: return ('half', index[half[1]])
    ordinary = re.fullmatch(r'3\.(.+)\.(inc|decnz)', op)
    if ordinary:
        return ('inc' if ordinary[2] == 'inc' else 'dec', index[ordinary[1]])
    raise ValueError(f'unknown operation: {op}')

leaves = []
def unfold(node, path):
    for bit, entry in enumerate(grammar['nodes'][node]):
        if 'node' in entry:
            unfold(entry['node'], path + str(bit))
        else:
            leaves.append((path + str(bit), entry['op']))
unfold(grammar['root'], '')
retained = [(path, op) for path, op in leaves if not op.startswith(('_break.', '_continue.'))]
number = {path: i for i, (path, _) in enumerate(retained)}
if len(number) != len(retained) or len(retained) != 177:
    raise ValueError('unexpected unfolded primitive graph')

def decode(control):
    node, code = grammar['root'], ''
    for i in range(163):
        bit = control[i] if i < len(control) else '0'
        code += bit
        entry = grammar['nodes'][node][int(bit)]
        if 'node' not in entry: return code, entry['op']
        node = entry['node']
    raise ValueError('grammar descent exhausted')

def transfer(code, op, branch):
    if op.startswith('_continue.'):
        count, seek, prefix = int(op.rsplit('.', 1)[1]), '1', code[:-1]
    else:
        count = int(op.rsplit('.', 1)[1]) + 1 if op.startswith('_break.') else 1
        if '.decnz' in op and branch: count = 2
        seek, prefix = '0', code
    for _ in range(count):
        j = prefix.rfind(seek)
        if j < 0: raise ValueError('missing lexical continuation')
        prefix = prefix[:j]
    return prefix + '1'

def settle(code):
    for _ in range(32):
        actual, op = decode(code)
        if actual != code: raise ValueError('not a complete leaf')
        if not op.startswith(('_break.', '_continue.')): return code
        code = decode(transfer(code, op, False))[0]
    raise ValueError('control-only chain exceeded bound')

expanded = []
for path, op in retained:
    action = parse(op)
    no = number[settle(decode(transfer(path, op, False))[0])]
    yes = number[settle(decode(transfer(path, op, True))[0])] if action[0] in ('dec', 'half') else no
    expanded.append((action, no, yes))

mapping, reverse = {}, {}
todo = deque([(invariant['core_graph']['entry'], number[settle('0')])])
while todo:
    src, dst = todo.popleft()
    if src in mapping:
        if mapping[src] != dst: raise ValueError('nonfunctional mapping')
        continue
    if dst in reverse: raise ValueError('duplicate retained entry')
    mapping[src], reverse[dst] = dst, src
    row = logical_rows[src]
    action = parse(row[0])
    target, no, yes = expanded[dst]
    if action[0] == 'move':
        _, source, dest = action
        if source == dest or target != ('dec', source):
            raise ValueError('move test mismatch')
        if expanded[no] != (('inc', dest), dst, dst):
            raise ValueError('move body mismatch')
        todo.append((row[1], yes))
    else:
        if target != action: raise ValueError('retained action mismatch')
        todo.append((row[1], no))
        if len(row) == 3: todo.append((row[2], yes))
if set(mapping) != set(range(len(logical_rows))):
    raise ValueError('unmapped contracted row')

for match in packet['matches']:
    entry, body = match['body']
    src, dst = index[match['source']], index[match['destination']]
    if expanded[entry] != (('dec', src), body, match['exit']) or expanded[body] != (('inc', dst), entry, entry):
        raise ValueError('producer move occurrence differs')

def lean_action(action):
    return '.' + action[0] + ''.join(' ' + str(i) for i in action[1:])

out = ['import Shared.PNP.Record285.OwnershipCore', '',
       '/-! Generated pre-contraction rows and contracted-to-expanded map. -/',
       'namespace Shared.PNP.Record285.OwnershipCore', '',
       'def expandedRows : Array Row := #[']
for i, (action, no, yes) in enumerate(expanded):
    out.append(f'  ⟨{lean_action(action)},{no},{yes}⟩' + (',' if i+1 < len(expanded) else ''))
out += [']', '', 'def expansionMap : Array Nat := #[' + ','.join(str(mapping[i]) for i in range(len(logical_rows))) + ']',
        '', 'end Shared.PNP.Record285.OwnershipCore', '']
generated = '\n'.join(out)
path = HERE / 'OwnershipExpandedData.lean'
if args.check:
    if path.read_text() != generated: raise ValueError('generated expanded data differs')
else:
    path.write_text(generated)
print(f'{len(expanded)} expanded rows; {len(mapping)} contracted entries; {len(packet["matches"])} move occurrences')
