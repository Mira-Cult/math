#!/usr/bin/env python3
"""Transcribe pinned producer grammar metadata; Lean checks literal table rows.

This generator and its metadata parsing are untrusted. `--check` only checks
reproducibility; the Lean row checks do not prove source-to-grammar semantics.
"""
import hashlib
import json
from pathlib import Path
import sys

root = Path(__file__).resolve().parents[1]
metadata = root / 'bindings/m236/producer-metadata.json'
out = root / 'lean/PASoundness/M236GrammarData.lean'
expected = 'cfd15b5d5eb62357ee4a9808d6e3cf044eab9ff2fdcbc1e8f0880046c5d4752e'
raw = metadata.read_bytes()
if hashlib.sha256(raw).hexdigest() != expected:
    raise ValueError('unexpected pinned metadata')
d = json.loads(raw)
g = d['grammar']; names = d['grammar_names']; ids = d['named_state_to_id']
if set(g) != {str(i) for i in range(158)} or d['grammar_root'] != 157:
    raise ValueError('unexpected grammar domain or root')

def edge(ch, b):
    if type(ch) is int:
        if not 0 <= ch < 158:
            raise ValueError('child outside grammar')
        return f'.node {ch}'
    if ch.startswith('emit.'):
        target = ids['6.continue.0' if b == 0 else '6.break.0']
        write, move, event = b == 0, 'left', 'some ' + ('true' if ch == 'emit.1' else 'false')
        if ch not in ('emit.0', 'emit.1'):
            raise ValueError('unknown output')
    elif ch.startswith('_continue.'):
        target = ids['6.continue.' + str(int(ch.split('.')[1]) - 1)]
        write, move, event = False, 'left', 'none'
    elif ch.startswith('_break.'):
        target = ids['6.break.' + ch.split('.')[1]]
        write, move, event = False, 'left', 'none'
    else:
        target = ids[ch]
        write, move, event = bool(b), 'right', 'none'
    return f'.leaf {json.dumps(ch)} {target} {str(write).lower()} .{move} ({event})'

lines = [
    'import PASoundness.M236GrammarCore', '',
    '/-! Generated from the retained pinned metadata by an untrusted generator.',
    'The actual row and event checks are in M236Grammar. -/',
    'namespace PASoundness.M236.Grammar', '',
    'def nodes : Vector Node 158 := #v[',
]
for i in range(158):
    a, b = g[str(i)]
    lines.append(f'  ⟨{ids[names[str(i)]]}, {edge(a, 0)}, {edge(b, 1)}⟩' + (',' if i < 157 else ''))
lines += [']', '', 'end PASoundness.M236.Grammar', '']
source = '\n'.join(lines)
if '--check' in sys.argv:
    if not out.exists() or out.read_text() != source:
        raise SystemExit('generated grammar differs')
    print('M236 grammar transcription matches pinned producer metadata')
else:
    out.write_text(source)
