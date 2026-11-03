#!/usr/bin/env python3
"""Extract the untrusted 21-register pre-projection primitive graph.

Lean independently checks its row-level renaming against the 18-register
graph. Frozen input provenance is checked here, not assumed as a proof.
"""
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

projection = load('producer-bank-projection.json',
                  '30546fc8cabd9d1d4a7aa749baa9ad9e7fdc2a34df4d9a201358af76bde169f8')
before = load('producer-pre-projection.json',
              '01b45f4fd580ba64a8d0e37cc5468281c2dc0202d2f6c5736af14cd9f641324d')
contraction = load('producer-ownership-contraction.json',
                   '8bc8909289c572829cc27a92d3d48689a38ba813cd98faae2f45cfc1cc0eda13')
after = contraction['before_grammar']
if before['nodes'] != after['nodes'] or before['root'] != after['root']:
    raise ValueError('projection changed grammar control')
if before['registers'] != projection['original_register_order'] or after['registers'] != projection['retained_register_order']:
    raise ValueError('register orders differ from producer packet')
if projection['removed_registers'] != ['$micro.r', '$micro.c', '$digit.index']:
    raise ValueError('unexpected removed registers')

def graph(grammar):
    names = {name: i for i, name in enumerate(grammar['registers'])}
    leaves = []
    def unfold(node, path):
        for bit, entry in enumerate(grammar['nodes'][node]):
            if 'node' in entry: unfold(entry['node'], path + str(bit))
            else: leaves.append((path + str(bit), entry['op']))
    unfold(grammar['root'], '')
    retained = [(path, op) for path, op in leaves if not op.startswith(('_break.', '_continue.'))]
    number = {path: i for i, (path, _) in enumerate(retained)}
    if len(number) != len(retained): raise ValueError('duplicate occurrence')

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

    def action(op):
        if op == 'beep': return ('beep',)
        half = re.fullmatch(r'3\.\$native-half:(.+)\.decnz', op)
        if half: return ('half', names[half[1]])
        normal = re.fullmatch(r'3\.(.+)\.(inc|decnz)', op)
        if normal: return ('inc' if normal[2] == 'inc' else 'dec', names[normal[1]])
        raise ValueError(f'unexpected operation {op}')

    out = []
    for path, op in retained:
        act = action(op)
        no = number[settle(decode(transfer(path, op, False))[0])]
        yes = number[settle(decode(transfer(path, op, True))[0])] if act[0] in ('dec', 'half') else no
        out.append((act, no, yes))
    if number[settle('0')] != 0 or len(out) != 177:
        raise ValueError('unexpected graph entry or size')
    return out, [path for path, _ in retained]

old, old_paths = graph(before)
new, _ = graph(after)
def lift(i): return i if i < 8 else i + 3
for i, ((old_op, old_no, old_yes), (new_op, new_no, new_yes)) in enumerate(zip(old, new)):
    expected = (new_op[0],) + tuple(lift(v) for v in new_op[1:])
    if (old_op, old_no, old_yes) != (expected, new_no, new_yes):
        raise ValueError(f'projection mismatch at row {i}')

def lean_action(action):
    return '.' + action[0] + ''.join(' ' + str(i) for i in action[1:])

out = ['import Shared.PNP.Record285.OwnershipCore', '',
       '/-! Generated pre-projection graph; Lean checks every row. -/',
       'namespace Shared.PNP.Record285.RegisterProjection',
       'open Shared.PNP.Record285.OwnershipCore', '',
       'def originalRows : Array Row := #[']
for i, (act, no, yes) in enumerate(old):
    out.append(f'  ⟨{lean_action(act)},{no},{yes}⟩' + (',' if i+1 < len(old) else ''))
out += [']', '', 'end Shared.PNP.Record285.RegisterProjection', '']
out.insert(-2, 'def originalPositions : Array (List Bool) := #[' +
           ','.join('[' + ','.join('true' if b == '1' else 'false' for b in path) + ']' for path in old_paths) + ']\n')
generated = '\n'.join(out)
path = HERE / 'ProjectionData.lean'
if args.check:
    if path.read_text() != generated: raise ValueError('generated projection data differs')
else:
    path.write_text(generated)
print(f'{len(old)} primitive rows; {len(before["registers"])} to {len(after["registers"])} registers')
