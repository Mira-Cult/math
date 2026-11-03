#!/usr/bin/env python3
"""Generate an untrusted core-graph certificate for Lean to check.

Inputs are byte-frozen copies of the accepted producer's grammar and late-zero
packet. The generator computes an occurrence-to-core correspondence; Lean
independently checks its rows and both outgoing branches.
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

grammar = load('producer-grammar.json',
               'b89fa51a9c90db473655aa94b74475104b4bdd3c7b73d13791a227d4a2599133')
packet = load('producer-late-zero.json',
              '0c52735985fa5ab3148140805879ad0066a5d168560fa9438f428149475960ea')
core = packet['after_context_graph']
if grammar['root'] != 162 or core['entry'] != 0:
    raise ValueError('unexpected graph entry')

def decode(control):
    node = grammar['root']
    code = ''
    for pos in range(163):
        b = control[pos] if pos < len(control) else '0'
        code += b
        edge = grammar['nodes'][node][int(b)]
        if 'node' not in edge:
            return code, edge['op']
        node = edge['node']
    raise ValueError('grammar descent exhausted')

def transfer(code, op, branch):
    if op.startswith('_continue.'):
        count = int(op.rsplit('.', 1)[1])
        seek, prefix = '1', code[:-1]
    else:
        count = (int(op.rsplit('.', 1)[1]) + 1) if op.startswith('_break.') else 1
        if ('.decnz' in op) and branch:
            count = 2
        seek, prefix = '0', code
    for _ in range(count):
        j = prefix.rfind(seek)
        if j < 0:
            raise ValueError(f'no control return for {code} {op}')
        prefix = prefix[:j]
    return prefix + '1'

def successor(code, op, branch):
    return decode(transfer(code, op, branch))[0]

def settle(code):
    for _ in range(3):
        actual, op = decode(code)
        if actual != code:
            raise ValueError('not a complete leaf address')
        if not op.startswith(('_break.', '_continue.')):
            return code
        code = successor(code, op, False)
    raise ValueError('administrative chain too long')

def edge(op):
    if op == 'beep':
        return '.beep'
    m = re.fullmatch(r'3\.\$coalesced\.(\d+)\.(inc|decnz)', op)
    if m:
        return ('.inc ' if m[2] == 'inc' else '.dec ') + m[1]
    m = re.fullmatch(r'3\.\$native-half:\$coalesced\.(\d+)\.decnz', op)
    if m:
        return '.half ' + m[1]
    raise ValueError(f'unexpected core action: {op}')

rows = core['rows']
mapping = {}
inverse = {}
todo = deque([(settle('0'), core['entry'])])
while todo:
    pc, i = todo.popleft()
    if i in mapping:
        if mapping[i] != pc:
            raise ValueError('core state has multiple addresses')
        continue
    if pc in inverse:
        raise ValueError('two core states have the same address')
    mapping[i] = pc
    inverse[pc] = i
    actual, op = decode(pc)
    spec = rows[i]
    if actual != pc or edge(op) != edge(spec[0]):
        raise ValueError(f'operation mismatch at {i}')
    todo.append((settle(successor(pc, op, False)), spec[1]))
    if len(spec) == 3:
        todo.append((settle(successor(pc, op, True)), spec[2]))
    elif len(spec) != 2:
        raise ValueError(f'unexpected graph row at {i}')
if set(mapping) != set(range(len(rows))):
    raise ValueError('core graph has unreachable rows')

def lean_code(pc):
    return '[' + ','.join('true' if b == '1' else 'false' for b in pc) + ']'

out = ['import Shared.PNP.Record285.GrammarCoreGraph', '',
       '/-! Generated data: Lean checks the transformation; the generator is untrusted. -/',
       'namespace Shared.PNP.Record285.GrammarCoreGraph', '',
       'def producerRows : Array CoreRow := #[']
for i, row in enumerate(rows):
    other = row[2] if len(row) == 3 else row[1]
    out.append(f'  ⟨{edge(row[0])},{row[1]},{other}⟩' + (',' if i+1 < len(rows) else ''))
out += [']', '', 'def producerPositions : Array (List Bool) := #[']
for i in range(len(rows)):
    out.append('  ' + lean_code(mapping[i]) + (',' if i+1 < len(rows) else ''))
out += [']', '', 'end Shared.PNP.Record285.GrammarCoreGraph', '']
generated = '\n'.join(out)
destination = HERE / 'GrammarCoreGraphData.lean'
if args.check:
    if destination.read_text() != generated:
        raise ValueError('generated data differs')
else:
    destination.write_text(generated)

# Reproduce the exact original field bytes, not a hash-derived statement.
packet_text = (HERE / 'producer-late-zero.json').read_text()
field_start = packet_text.index('"after_context_graph"')
object_start = packet_text.index('{', field_start)
parsed, field_end = json.JSONDecoder().raw_decode(packet_text, object_start)
if parsed != core:
    raise ValueError('incorrect core-graph extraction')
fragment = packet_text[field_start:field_end]
header = '"after_context_graph": {\n    "entry": 0,\n    "rows": [\n'
suffix = '    ]\n  }'
row_text = []
for i, row in enumerate(rows):
    rendered = '\n'.join('      ' + line for line in json.dumps(row, indent=2).splitlines())
    row_text.append(rendered + ('\n' if i+1 == len(rows) else ',\n'))
if header + ''.join(row_text) + suffix != fragment:
    raise ValueError('unexpected source graph serialization')

def chars(text):
    def char(c):
        if c == '\n': return "'\\n'"
        if c == "'": return "'\\\''"
        if c == '\\': return "'\\\\'"
        if not 32 <= ord(c) <= 126: raise ValueError('non-ASCII character')
        return "'" + c + "'"
    return ','.join(map(char, text))

blocks = [range(i, min(i+4, len(rows))) for i in range(0, len(rows), 4)]
cert = [
    'import Shared.PNP.Record285.GrammarCoreGraphText', '',
    '/-! Generated exact fragment-to-typed-data certificate. -/',
    'set_option maxRecDepth 131072', 'set_option maxHeartbeats 0',
    'namespace Shared.PNP.Record285.GrammarCoreGraph', '',
    'def sourceChars : List Char := [' + chars(fragment) + ']',
    'theorem source_chars : sourceFragment = String.ofList sourceChars := by rfl', '',
    'def headerChars : List Char := [' + chars(header) + ']',
    'def suffixChars : List Char := [' + chars(suffix) + ']', '',
]
for block_no, block in enumerate(blocks):
    entries = []
    for i in block:
        row = rows[i]
        other = row[2] if len(row) == 3 else row[1]
        last = 'true' if i+1 == len(rows) else 'false'
        entries.append(f'(⟨{edge(row[0])},{row[1]},{other}⟩,{last})')
    cert += [f'def entries{block_no} : List (CoreRow × Bool) := [' + ','.join(entries) + ']',
             f'def chars{block_no} : List Char := [' + chars(''.join(row_text[i] for i in block)) + ']',
             f'theorem chars_ok{block_no} : renderEntries entries{block_no} = chars{block_no} := by decide', '']
count = len(blocks)
cert += [f'def entriesFrom{count} : List (CoreRow × Bool) := []',
         f'def charsFrom{count} : List Char := []',
         f'theorem charsFrom_ok{count} : renderEntries entriesFrom{count} = charsFrom{count} := rfl', '']
for i in range(count-1, -1, -1):
    j = i+1
    cert += [f'def entriesFrom{i} : List (CoreRow × Bool) := entries{i} ++ entriesFrom{j}',
             f'def charsFrom{i} : List Char := chars{i} ++ charsFrom{j}',
             f'theorem charsFrom_ok{i} : renderEntries entriesFrom{i} = charsFrom{i} := by',
             f'  change renderEntries (entries{i} ++ entriesFrom{j}) = chars{i} ++ charsFrom{j}',
             f'  rw [renderEntries_append, chars_ok{i}, charsFrom_ok{j}]', '']
cert += ['theorem chars_concat : sourceChars = headerChars ++ charsFrom0 ++ suffixChars := by rfl', '',
         'theorem source_serialized : sourceFragment =',
         '    String.ofList (headerChars ++ renderEntries entriesFrom0 ++ suffixChars) := by',
         '  rw [source_chars, chars_concat, charsFrom_ok0]', '',
         'theorem source_rows : producerRows = (entriesFrom0.map Prod.fst).toArray := by decide', '',
         'end Shared.PNP.Record285.GrammarCoreGraph', '']
generated_cert = '\n'.join(cert)
for path, content in [(HERE / 'producer-core-fragment.txt', fragment),
                      (HERE / 'GrammarCoreGraphTextCertificate.lean', generated_cert)]:
    if args.check:
        if path.read_text() != content:
            raise ValueError(f'generated data differs: {path.name}')
    else:
        path.write_text(content)
print(f'{len(rows)} core rows; {len(mapping)} occurrence addresses')
