#!/usr/bin/env python3
"""Generate untrusted typed producer grammar and exact-text Lean certificate."""
import argparse
from hashlib import sha256
import json
from pathlib import Path
import re

here = Path(__file__).resolve().parent
parser = argparse.ArgumentParser()
parser.add_argument('--check', action='store_true')
parser.add_argument('--pre-control', action='store_true')
args = parser.parse_args()
if args.pre_control:
    source, expected, size, expected_root = ('producer-pre-control.json', '88da402c7c2ed088192edddead7c2ee26f787135440832c6128e247fb409b00d', 183, 182)
    ns, prefix = 'PreControlGrammar', 'PreControlGrammar'
else:
    source, expected, size, expected_root = ('producer-pre-projection.json', '01b45f4fd580ba64a8d0e37cc5468281c2dc0202d2f6c5736af14cd9f641324d', 182, 181)
    ns, prefix = 'ProducerGrammar', 'ProjectionGrammar'
raw = (here / source).read_bytes()
if sha256(raw).hexdigest() != expected:
    raise ValueError('unexpected grammar source')
text = raw.decode('ascii')
g = json.loads(text)
if json.dumps(g, indent=2) + '\n' != text:
    raise ValueError('unexpected JSON format')
nodes, names, root = g['nodes'], g['registers'], g['root']
if len(nodes) != size or len(names) != 21 or root != expected_root or len(set(names)) != len(names):
    raise ValueError('unexpected grammar dimensions')
numbers = {name: i for i, name in enumerate(names)}

def edge(e):
    if set(e) == {'node'}: return f'.node {e["node"]}'
    s = e['op']
    if s == 'beep': return '.beep'
    if m := re.fullmatch(r'_(break|continue)\.(\d+)', s):
        return f'.{"brk" if m[1] == "break" else "cont"} {m[2]}'
    if m := re.fullmatch(r'3\.\$native-half:(.+)\.decnz', s):
        return f'.half {numbers[m[1]]}'
    if m := re.fullmatch(r'3\.(.+)\.(inc|decnz)', s):
        return f'.{"inc" if m[2] == "inc" else "dec"} {numbers[m[1]]}'
    raise ValueError(f'unrecognized edge: {e}')

def chars(s):
    def char(c):
        if c == '\n': return "'\\n'"
        if c == "'": return "'\\\''"
        if c == '\\': return "'\\\\'"
        if not 32 <= ord(c) <= 126: raise ValueError('non-ASCII character')
        return "'" + c + "'"
    return ','.join(map(char, s))

def emit(name, content):
    p = here / name
    if args.check:
        if p.read_text() != content: raise ValueError(f'generated source differs: {name}')
    else: p.write_text(content)

def node_text(node, last):
    return '\n'.join('    ' + line for line in json.dumps(node, indent=2).splitlines()) + ('\n' if last else ',\n')

texts = [node_text(n, i == len(nodes)-1) for i, n in enumerate(nodes)]
header = '{\n  "nodes": [\n'
suffix = text[len(header) + sum(map(len, texts)):]
assert header + ''.join(texts) + suffix == text
chunks = [range(i, min(i+4, len(nodes))) for i in range(0, len(nodes), 4)]
base = ['import Shared.PNP.Record285.ProjectionGrammarText', '', f'namespace Shared.PNP.Record285.{ns}', 'open Shared.PNP.Record285.Grammar', '']
if args.pre_control:
    base += ['open Shared.PNP.Record285.ProducerGrammar', 'def literal : String := include_str "producer-pre-control.json"', '']
for c, idxs in enumerate(chunks):
    entries = [f'(({edge(nodes[i][0])}, {edge(nodes[i][1])}), {str(i == len(nodes)-1).lower()})' for i in idxs]
    base.append(f'def entries{c} : List Entry := [' + ', '.join(entries) + ']')
base.append(f'def entriesFrom{len(chunks)} : List Entry := []')
for c in reversed(range(len(chunks))):
    base.append(f'def entriesFrom{c} : List Entry := entries{c} ++ entriesFrom{c+1}')
base += ['def entries : List Entry := entriesFrom0', 'def fastNodes : Array Node := #[' + ', '.join(f'({edge(n[0])}, {edge(n[1])})' for n in nodes) + ']',
         'def grammar : Data := ⟨fastNodes, #[' + ', '.join(json.dumps(n) for n in names) + f'], {root}⟩',
         'theorem nodes_exact : grammar.nodes = (entries.map Prod.fst).toArray := by rfl', '', f'end Shared.PNP.Record285.{ns}', '']
emit(f'{prefix}Data.lean', '\n'.join(base))
out = [f'import Shared.PNP.Record285.{prefix}Data', '', 'set_option maxRecDepth 131072', 'set_option maxHeartbeats 0', '', f'namespace Shared.PNP.Record285.{ns}', 'open Shared.PNP.Record285.Grammar', *(['open Shared.PNP.Record285.ProducerGrammar'] if args.pre_control else []), '',
       'def literalChars : List Char := [' + chars(text) + ']', 'theorem literal_chars : literal = String.ofList literalChars := by rfl', '',
       'def headerChars : List Char := [' + chars(header) + ']', 'def suffixChars : List Char := [' + chars(suffix) + ']',
       'theorem suffix_correct : renderSuffix grammar = suffixChars := by decide', '']
for c, idxs in enumerate(chunks):
    out += [f'def chars{c} : List Char := [' + chars(''.join(texts[i] for i in idxs)) + ']',
            f'theorem chars_ok{c} : renderEntries grammar.names entries{c} = chars{c} := by decide', '']
out += [f'def charsFrom{len(chunks)} : List Char := []',
        f'theorem rendered{len(chunks)} : renderEntries grammar.names entriesFrom{len(chunks)} = charsFrom{len(chunks)} := rfl', '']
for c in reversed(range(len(chunks))):
    out += [f'def charsFrom{c} : List Char := chars{c} ++ charsFrom{c+1}',
            f'theorem rendered{c} : renderEntries grammar.names entriesFrom{c} = charsFrom{c} := by',
            f'  change renderEntries grammar.names (entries{c} ++ entriesFrom{c+1}) = chars{c} ++ charsFrom{c+1}',
            f'  rw [{"ProducerGrammar." if args.pre_control else ""}renderEntries_append, chars_ok{c}, rendered{c+1}]', '']
out += ['theorem chars_concat : literalChars = headerChars ++ charsFrom0 ++ suffixChars := by rfl', '',
        '/-- The literal source bytes are the serialization of these exact typed nodes, names and root. -/',
        'theorem literal_serialization : literal = String.ofList (headerChars ++ renderEntries grammar.names entries ++ renderSuffix grammar) := by',
        '  rw [literal_chars, chars_concat, suffix_correct]',
        '  change _ = String.ofList (headerChars ++ renderEntries grammar.names entriesFrom0 ++ suffixChars)',
        '  rw [rendered0]', '', f'end Shared.PNP.Record285.{ns}', '']
emit(f'{prefix}TextCertificate.lean', '\n'.join(out))
print(f'{len(nodes)} nodes; {len(names)} registers; {len(chunks)} exact-text segments')
