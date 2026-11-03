#!/usr/bin/env python3
"""Generate an untrusted occurrence map for the pre-control producer grammar."""
import argparse
from hashlib import sha256
import json
from pathlib import Path
import runpy
import sys

here = Path(__file__).resolve().parent
parser = argparse.ArgumentParser()
parser.add_argument('--check', action='store_true')
args = parser.parse_args()
raw = (here / 'producer-pre-control.json').read_bytes()
if sha256(raw).hexdigest() != '88da402c7c2ed088192edddead7c2ee26f787135440832c6128e247fb409b00d':
    raise ValueError('unexpected pre-control grammar')
# Importing the extractor verifies, but never changes, its independently
# generated 21-register graph. Lean checks the occurrence map separately.
sys.argv = [str(here / 'generate_projection.py'), '--check']
extract = runpy.run_path(str(here / 'generate_projection.py'))
rows, paths = extract['graph'](json.loads(raw))
if rows != extract['old']:
    raise ValueError('pre-control primitive graph differs')
positions = ','.join('[' + ','.join('true' if b == '1' else 'false' for b in path) + ']' for path in paths)
out = '\n'.join(['import Shared.PNP.Record285.PreControlGrammarData', '',
    '/-! Untrusted occurrence map; checked against the full grammar in Lean. -/',
    'namespace Shared.PNP.Record285.PreControlGrammar', '',
    f'def positions : Array (List Bool) := #[{positions}]', '',
    'end Shared.PNP.Record285.PreControlGrammar', ''])
p = here / 'PreControlPositions.lean'
if args.check:
    if p.read_text() != out: raise ValueError('generated positions differ')
else:
    p.write_text(out)
print(f'{len(rows)} pre-control primitive occurrences')
