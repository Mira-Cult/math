"""Deterministic complete build; tables and semantic IR are canonical artifacts."""
from __future__ import annotations

import argparse
from collections import Counter
import hashlib
import json
from pathlib import Path

from natural import NaturalBuilder
from backend import add_literal_initializer, totalize_silently, leaf_paths
from machine import Machine, emit, parse

ROOT = Path(__file__).resolve().parent.parent


def dump(path, value):
    path.write_text(json.dumps(value, sort_keys=True, indent=2) + '\n')


def canonicalize(builder):
    states = {q for q, b in builder.tm.states}
    names = [builder.tm.start, 'B'] + sorted(states - {builder.tm.start, 'B'})
    mapping = {q: i for i, q in enumerate(names)}
    rows = {(mapping[q], int(b)): (int(t.write), -1 if t.direction == 'L' else 1, mapping[t.nextstate])
            for (q, b), t in builder.tm.states.items()}
    return Machine(0, 1, rows), mapping


def grammar(builder):
    live = sorted(builder.reachable())
    remap = {old: new for new, old in enumerate(live)}
    return dict(registers=list(builder.registers),
                root=remap[builder.find_seq('main().0')],
                nodes=[[{'node': remap[v]} if isinstance(v, int) else {'op': str(v)}
                        for v in builder.sequences[i].seq] for i in live])


def build(output, variant='baseline', source=None):
    output = Path(output)
    output.mkdir(parents=True, exist_ok=True)
    source = ROOT / 'code/source_baseline.py' if source is None else Path(source)
    b = NaturalBuilder(source.read_text()).build_machine()
    ir = grammar(b)
    if variant == 'baseline':
        initializer = add_literal_initializer(b)
    elif variant == 'compact-init':
        # Pinned 5-state bootstrap and its 3-state continuation adapter.
        # Finite exact simulation verifies the entry configuration independently.
        initializer = dict(kind='pinned-bootstrap', entry='main().0', head=-3818,
                           prefix=[-3821, -3820], zero_block_positions=[3, 3821, 2])
        assert len(b.registers) <= 1909
        assert max(len(p) for p, op in leaf_paths(b)) < 3822
    else:
        raise ValueError('unknown build variant')
    missing = totalize_silently(b)
    b.tm.gc()
    machine, mapping = canonicalize(b)
    table_path = output / (variant + '.tm')
    emit(machine, table_path)
    assert parse(table_path).rows == machine.rows
    dump(output / (variant + '.ir.json'), ir)
    profile = Counter()
    for name in mapping:
        if name.startswith('init.'):
            module = 'blank initialization'
        elif name.startswith('3.'):
            module = 'register operations'
        elif name[0].isdigit():
            module = 'register engine and dispatch'
        elif name in ('beep', 'B'):
            module = 'beep primitive'
        elif name == 'silent.sink':
            module = 'totalization'
        else:
            module = 'compiled arithmetic and control'
        profile[module] += 1
    metadata = dict(variant=variant, states=machine.count, transitions=len(machine.rows),
                    start=machine.start, B=machine.beep, source_sha256=hashlib.sha256(source.read_bytes()).hexdigest(),
                    sha256=hashlib.sha256(table_path.read_bytes()).hexdigest(),
                    ir_sha256=hashlib.sha256((output / (variant + '.ir.json')).read_bytes()).hexdigest(),
                    registers=len(b.registers), profile=dict(profile), initializer=initializer,
                    totalized_missing_rows=missing,
                    state_names=mapping)
    dump(output / (variant + '.json'), metadata)
    return metadata


if __name__ == '__main__':
    ap = argparse.ArgumentParser()
    ap.add_argument('--out', type=Path, required=True)
    ap.add_argument('--variant', choices=('baseline', 'compact-init'), default='baseline')
    args = ap.parse_args()
    result = build(args.out, args.variant)
    print(json.dumps({k: result[k] for k in ('variant', 'states', 'transitions', 'sha256', 'registers', 'profile')}, indent=2))
