#!/usr/bin/env python3
"""Generate untrusted reverse masks for all preserving operation terminals.

Lean independently checks the masks' seeds, edge closure, and root bound.
"""
import argparse
from pathlib import Path

import generate_dispatch_invariant as base

HERE = Path(__file__).resolve().parent
INCREMENTS = tuple(base.TERMINALS)
SEEDS = INCREMENTS + tuple(q - 1 for q in INCREMENTS) + (105, 106, 107, 108, 121)


def render():
    base.TERMINALS = SEEDS
    _, masks = base.masks(base.rows())
    lines = ",\n".join(
        "  " + ", ".join(str(x) for x in masks[i:i + 15])
        for i in range(0, len(masks), 15)
    )
    return """import Shared.PNP.Record285.GrammarGraphCheck

/-! Generated reverse masks; only checked closure and seeds establish meaning. -/
namespace Shared.PNP.Record285.OperationInvariantData

def backwardData : Array Nat := #[
""" + lines + """
]

end Shared.PNP.Record285.OperationInvariantData
"""


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--check", action="store_true")
    args = parser.parse_args()
    target = HERE / "OperationInvariantData.lean"
    content = render()
    if args.check:
        if target.read_text() != content:
            raise SystemExit("operation masks differ from deterministic extraction")
        print("operation masks match; Lean checks their meaning")
    else:
        target.write_text(content)
        print("wrote", target)


if __name__ == "__main__":
    main()
