#!/usr/bin/env python3
"""Transcribe the pinned untrusted occurrence-graph witness into Lean data.

The accompanying Lean checks compare this witness with literal grammar control.
They do not prove that executing the producer source constructs this graph.
"""
import hashlib
import json
from pathlib import Path
import sys

root = Path(__file__).resolve().parents[1]
source = root / 'bindings/m236/occurrence-graph.json'
out = root / 'lean/PASoundness/M236OccurrenceGraphData.lean'
raw = source.read_bytes()
expected = 'dbad7675ad75b28ff70f26387f0cb6cbeabe5dea586d681eefa47c11c422ae93'
if hashlib.sha256(raw).hexdigest() != expected:
    raise ValueError('unexpected pinned occurrence graph')
rows = json.loads(raw)
if len(rows) != 760 or any(not isinstance(row, list) or len(row) not in (2, 3)
                            or not isinstance(row[0], str)
                            or any(type(n) is not int or not 0 <= n < 760 for n in row[1:])
                            for row in rows):
    raise ValueError('invalid occurrence graph')
lines = ['import PASoundness.M236AdjacentUnique', '',
         '/-! Generated from the retained untrusted occurrence-graph witness. -/',
         'namespace PASoundness.M236.OccurrenceGraph', '',
         'def sourceRows : Array (String × Nat × Option Nat) := #[']
for row in rows:
    operation, target, *zero = row
    extra = f'some {zero[0]}' if zero else 'none'
    lines.append(f'  ({json.dumps(operation)}, {target}, {extra}),')
lines += [']', '', 'end PASoundness.M236.OccurrenceGraph', '']
result = '\n'.join(lines)

if '--check' in sys.argv:
    if not out.exists() or out.read_text() != result:
        raise SystemExit('generated occurrence graph differs')
    print('M236 occurrence graph transcription matches pinned witness')
else:
    out.write_text(result)
