#!/usr/bin/env python3
"""Complete interaction prices for ordered atoms and the Cantor constructor tag."""
from __future__ import annotations
import argparse
import json
import sys
from pathlib import Path
import strict_atoms

ROOT = Path(__file__).resolve().parent
sys.path.insert(0, str(ROOT.parent))
import cantor_tagged

p = strict_atoms.p


class OrderedCantor(cantor_tagged.CantorTagged, strict_atoms.ordered_atoms.OrderedAtoms):
    pass


class StrictCantor(cantor_tagged.CantorTagged, strict_atoms.StrictAtoms):
    pass


CLASSES = {cls.__name__: cls for cls in (OrderedCantor, StrictCantor)}


if __name__ == '__main__':
    parser = argparse.ArgumentParser()
    parser.add_argument('--out', type=Path, required=True)
    parser.add_argument('--class-name', choices=CLASSES, required=True)
    args = parser.parse_args()
    if args.out.exists():
        raise ValueError('Fresh output directory required')
    print(json.dumps(p.opt.compile_candidate(CLASSES[args.class_name], args.out)[1], indent=2))
