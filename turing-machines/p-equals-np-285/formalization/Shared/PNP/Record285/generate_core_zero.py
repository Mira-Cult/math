#!/usr/bin/env python3
"""Extract the producer's pre-elimination core graph and occurrence masks.

The output is untrusted data. Lean must independently check the transfer
invariant, the zero-test locations, and any relation to the later core graph.
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
raw = (HERE / 'producer-late-zero.json').read_bytes()
if sha256(raw).hexdigest() != '0c52735985fa5ab3148140805879ad0066a5d168560fa9438f428149475960ea':
    raise ValueError('unexpected producer packet')
p = json.loads(raw)
grammar = p['input_grammar']
core = p['input_core_graph']
states = p['contextual_certificate']['states_at_occurrences']

occurrences = []
def unfold(n, path):
    for bit, entry in enumerate(grammar['nodes'][n]):
        if 'node' in entry:
            unfold(entry['node'], path + str(bit))
        else:
            occurrences.append((path + str(bit), entry['op']))
unfold(grammar['root'], '')
if len(occurrences) != len(states):
    raise ValueError('mask/occurrence count mismatch')
by_path = {path: (i, op, states[i]) for i, (path, op) in enumerate(occurrences)}
if len(by_path) != len(occurrences):
    raise ValueError('duplicate occurrence address')

def decode(control):
    node, code = grammar['root'], ''
    for i in range(163):
        bit = control[i] if i < len(control) else '0'
        code += bit
        entry = grammar['nodes'][node][int(bit)]
        if 'node' not in entry:
            return code, entry['op']
        node = entry['node']
    raise ValueError('grammar descent exhausted')

def transfer(code, op, branch):
    if op.startswith('_continue.'):
        count, seek, prefix = int(op.rsplit('.', 1)[1]), '1', code[:-1]
    else:
        count = int(op.rsplit('.', 1)[1]) + 1 if op.startswith('_break.') else 1
        if '.decnz' in op and branch:
            count = 2
        seek, prefix = '0', code
    for _ in range(count):
        j = prefix.rfind(seek)
        if j < 0:
            raise ValueError('missing lexical continuation')
        prefix = prefix[:j]
    return prefix + '1'

def settle(code):
    for _ in range(16):
        actual, op = decode(code)
        if actual != code:
            raise ValueError('not a leaf path')
        if not op.startswith(('_break.', '_continue.')):
            return code
        code = decode(transfer(code, op, False))[0]
    raise ValueError('control-only chain not bounded')

rows, mapping, inverse = core['rows'], {}, {}
todo = deque([(settle('0'), core['entry'])])
while todo:
    path, index = todo.popleft()
    if index in mapping:
        if mapping[index] != path:
            raise ValueError('nonfunctional index mapping')
        continue
    if path in inverse:
        raise ValueError('duplicate primitive occurrence')
    mapping[index], inverse[path] = path, index
    actual, op = decode(path)
    row = rows[index]
    if actual != path or op != row[0]:
        raise ValueError('core operation mismatch')
    todo.append((settle(decode(transfer(path, op, False))[0]), row[1]))
    if len(row) == 3:
        todo.append((settle(decode(transfer(path, op, True))[0]), row[2]))
    elif len(row) != 2:
        raise ValueError('invalid source core row')
if set(mapping) != set(range(len(rows))):
    raise ValueError('unreachable core row')

def edge(op):
    if op == 'beep':
        return '.beep'
    m = re.fullmatch(r'3\.\$coalesced\.(\d+)\.(inc|decnz)', op)
    if m:
        return ('.inc ' if m[2] == 'inc' else '.dec ') + m[1]
    m = re.fullmatch(r'3\.\$native-half:\$coalesced\.(\d+)\.decnz', op)
    if m:
        return '.half ' + m[1]
    raise ValueError(f'unexpected operation: {op}')

masks = []
for i in range(len(rows)):
    _, _, mask = by_path[mapping[i]]
    if mask is None or len(mask) != 15 or any(c not in '1234567' for c in mask):
        raise ValueError(f'bad or unreachable primitive mask: {i}')
    masks.append([int(c) for c in mask])

selected = []
for entry in p['candidates']:
    occ = entry['occurrence']
    path, op = occurrences[occ]
    # The producer records paths with its explicit outer '110' prefix.
    if op != entry['operation'] or '110' + path != entry['path']:
        raise ValueError('selected occurrence path or operation differs')
    selected.append(inverse[path])
if selected != [12, 53, 130, 152, 168]:
    raise ValueError('selected input-graph positions differ')

# Match each retained post-elimination row to its input occurrence. Only the
# selected zero branch may be bypassed, and at most one such row is skipped.
output_rows = p['after_context_graph']['rows']
selected_set = set(selected)
def skip(index):
    if index not in selected_set:
        return index
    row = rows[index]
    if len(row) != 3 or row[2] in selected_set:
        raise ValueError('unexpected zero-contraction chain')
    return row[2]

core_map, seen_input = {}, set()
todo = deque([(skip(core['entry']), p['after_context_graph']['entry'])])
while todo:
    old, new = todo.popleft()
    if new in core_map:
        if core_map[new] != old:
            raise ValueError('nonfunctional rewrite mapping')
        continue
    if old in seen_input:
        raise ValueError('duplicate retained occurrence')
    core_map[new] = old
    seen_input.add(old)
    old_row, new_row = rows[old], output_rows[new]
    if old_row[0] != new_row[0] or len(old_row) != len(new_row):
        raise ValueError('retained operation differs')
    for old_next, new_next in zip(old_row[1:], new_row[1:]):
        todo.append((skip(old_next), new_next))
if set(core_map) != set(range(len(output_rows))):
    raise ValueError('unmapped post-elimination row')

out = ['import Shared.PNP.Record285.GrammarCoreGraph', '',
       '/-! Generated pre-elimination graph and occurrence masks. -/',
       'namespace Shared.PNP.Record285.GrammarCoreZero',
       'open Shared.PNP.Record285.GrammarCoreGraph', '',
       'def inputRows : Array CoreRow := #[']
for i, row in enumerate(rows):
    yes = row[2] if len(row) == 3 else row[1]
    out.append(f'  ⟨{edge(row[0])},{row[1]},{yes}⟩' + (',' if i+1 < len(rows) else ''))
out += [']', '', 'def masks : Array (Array Nat) := #[']
for i, mask in enumerate(masks):
    out.append('  #[' + ','.join(map(str, mask)) + ']' + (',' if i+1 < len(masks) else ''))
out += [']', '', 'def zeroRows : List Nat := [' + ','.join(map(str, selected)) + ']',
        '', 'def retainedMap : Array Nat := #[' + ','.join(str(core_map[i]) for i in range(len(output_rows))) + ']',
        '', 'end Shared.PNP.Record285.GrammarCoreZero', '']
generated = '\n'.join(out)
path = HERE / 'GrammarCoreZeroData.lean'
if args.check:
    if path.read_text() != generated:
        raise ValueError('generated data differs')
else:
    path.write_text(generated)
print(f'{len(rows)} input rows; {len(masks)} masks; selected {selected}')
