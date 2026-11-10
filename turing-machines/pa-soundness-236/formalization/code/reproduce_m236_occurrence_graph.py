#!/usr/bin/env python3
"""Reproduce the M236 occurrence witness from an archived producer checkout.

This is an untrusted conventional reconstruction, not a Lean proof that the
producer's Python execution implements the mathematical source program.
"""
import argparse
import hashlib
import json
from pathlib import Path
import sys

parser = argparse.ArgumentParser()
parser.add_argument('--producer-root', type=Path, required=True,
                    help='root of an archive of producer commit bad500e2')
parser.add_argument('--check', action='store_true')
args = parser.parse_args()
root = args.producer_root.resolve() / 'problems/pa-full-soundness/experiments/pa266-architecture-20261031'
sys.path[:0] = [str(root), str(root / 'architecture')]
import fused_beam

p = fused_beam.beam_rebind.p
base = fused_beam.beam_rebind.parent.Base(p.opt.SOURCE)
base.build_tree()
before = p.gs.graph(base)
selected = fused_beam.FusedBeam(p.opt.SOURCE)
selected.build_tree()
after = p.gs.graph(selected)
if before != after:
    raise ValueError('selected grammar changes the source occurrence graph')
raw = (json.dumps(before, separators=(',', ':')) + '\n').encode()
expected = 'dbad7675ad75b28ff70f26387f0cb6cbeabe5dea586d681eefa47c11c422ae93'
if hashlib.sha256(raw).hexdigest() != expected or len(before) != 760 or sum(len(row) - 1 for row in before) != 1036:
    raise ValueError('unexpected occurrence graph')
destination = Path(__file__).resolve().parents[1] / 'bindings/m236/occurrence-graph.json'
if args.check:
    if destination.read_bytes() != raw:
        raise SystemExit('retained occurrence witness differs')
    print('M236 producer occurrence graph matches retained witness (760 rows, 1036 edges)')
else:
    destination.write_bytes(raw)
