#!/usr/bin/env python3
"""Transcribe pinned bit-events-v1 rows and quotient map into Lean literals.

This is an untrusted generator; the resulting finite data and proofs are checked
by Lean. The SHA pins bind the source files, not their semantic correctness.
"""
import hashlib
import json
from pathlib import Path
import sys

root = Path(__file__).resolve().parents[1]
bind = root / 'bindings' / 'm236'
out = root / 'lean' / 'PASoundness' / 'M236Data.lean'
expected = {
    'machine.tm': 'bcf4a1fd22e9959a4145688d05ec20591d97967050ad1a16beeb22a187edaedc',
    'raw.tm': 'e73b3c7fbcbbc4614e4ee33a6e33cacfb3b8e2dc32822591db2afdfedf01a9e8',
    'quotient.json': '23491bc2faecf603190bab3ebbae89ab7fe7bf019f1b075ae1499183df4eae01',
}

def parse(name, n):
    data = (bind / name).read_bytes()
    if hashlib.sha256(data).hexdigest() != expected[name]:
        raise ValueError(f'{name}: wrong hash')
    lines = data.decode('ascii').splitlines()
    if lines[:5] != ['#! format bit-events-v1', f'#! states {n}', '#! start 0', '#! blank 0', '#! head 0']:
        raise ValueError('unexpected header')
    rows = []
    for i, line in enumerate(lines[5:]):
        p = line.split()
        if len(p) != 6 or p[0] != str(i // 2) or p[1] != str(i % 2):
            raise ValueError(f'{name}: invalid row order at {i}')
        q, read, write, move, target, event = p
        if write not in ('0','1') or move not in ('L','R') or event not in ('-','0','1') or not target.isdigit() or not 0 <= int(target) < n:
            raise ValueError(f'{name}: invalid row {i}')
        rows.append((write == '1', move, int(target), event))
    if len(rows) != 2*n:
        raise ValueError(f'{name}: wrong row count')
    return rows

def row(r):
    write, move, target, _ = r
    return f'⟨{str(write).lower()}, .{"left" if move == "L" else "right"}, {target}, false⟩'

def label(r):
    return {'-':'none', '0':'some false', '1':'some true'}[r[3]]

def make(name, n, rows):
    out = [f'def {name} : Machine {n} where', '  table := ⟨#v[']
    for i in range(n):
        out.append(f'    ({row(rows[2*i])}, {row(rows[2*i+1])})' + (',' if i+1<n else ''))
    out += ['  ]⟩', '  start := 0', '  blank := false', '  startHead := 0', '', f'def {name}Labels : BitLabels {n} := #v[']
    for i in range(n):
        out.append(f'  ({label(rows[2*i])}, {label(rows[2*i+1])})' + (',' if i+1<n else ''))
    return '\n'.join(out + [']', ''])

a = parse('raw.tm', 237)
b = parse('machine.tm', 236)
metadata = (bind / 'quotient.json').read_bytes()
if hashlib.sha256(metadata).hexdigest() != expected['quotient.json']:
    raise ValueError('quotient.json: wrong hash')
mapping = json.loads(metadata)['quotient']['state_map']
if len(mapping) != 237 or any(type(i) is not int or not 0 <= i < 236 for i in mapping):
    raise ValueError('invalid quotient map')
source = '''import PASoundness.Machine

/-! Generated literal input. See `code/generate_m236.py` and `bindings/m236`.
Both machines start on a blank two-way tape. Event labels belong to the
transition taken and are kept separately from the scalar beep field. -/
namespace PASoundness.M236
open Shared.Beeping.Machines

'''
source += make('raw', 237, a) + '\n' + make('machine', 236, b)
source += '\ndef quotientMap : Vector (Fin 236) 237 := #v[\n  '
source += ', '.join(map(str, mapping)) + '\n]\n\nend PASoundness.M236\n'
if '--check' in sys.argv:
    if not out.exists() or out.read_text() != source:
        raise SystemExit('generated Lean differs')
    print('M236 generated Lean matches pinned inputs')
else:
    out.write_text(source)
