#!/usr/bin/env python3
"""Generate untrusted reverse masks for all grammar control-leaf parents.

Lean independently checks each seed, edge closure and root bound. The
generator reads the frozen producer grammar and its existing Lean state map.
"""
import argparse
import json
import re
from pathlib import Path

import generate_dispatch_invariant as base

HERE = Path(__file__).resolve().parent


def render():
    text = (HERE / "GrammarData.lean").read_text()
    found = re.search(r"def stateMap : Array Nat := #\[([^]]+)\]", text)
    if not found:
        raise ValueError("missing grammar state map")
    states = [int(part.strip()) for part in found.group(1).split(",")]
    nodes = json.loads((HERE / "producer-grammar.json").read_text())["nodes"]
    if len(states) != len(nodes) or len(nodes) != 163:
        raise ValueError("unexpected grammar size")
    base.TERMINALS = [states[i] for i, node in enumerate(nodes)
                      if node[1].get("op", "").startswith(("_break.", "_continue."))]
    _, masks = base.masks(base.rows())
    lines = ",\n".join("  " + ", ".join(str(x) for x in masks[i:i+15])
                         for i in range(0, len(masks), 15))
    return """import Shared.PNP.Record285.GrammarGraph

/-! Generated reverse masks; Lean separately checks the seeds and closure. -/
namespace Shared.PNP.Record285.ControlInvariantData

def backwardData : Array Nat := #[
""" + lines + """
]

end Shared.PNP.Record285.ControlInvariantData
"""


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--check", action="store_true")
    args = parser.parse_args()
    target = HERE / "ControlInvariantData.lean"
    content = render()
    if args.check:
        if target.read_text() != content:
            raise SystemExit("control masks differ from deterministic extraction")
        print("control masks match; Lean checks their meaning")
    else:
        target.write_text(content)
        print("wrote", target)


if __name__ == "__main__":
    main()
