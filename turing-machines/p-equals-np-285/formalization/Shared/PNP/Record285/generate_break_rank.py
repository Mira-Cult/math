#!/usr/bin/env python3
"""Generate untrusted lower bounds on zero bits along preserving routes.

Lean checks the initial value, every reachable preserving edge and the
break-leaf bounds. Distances are capped at three.
"""
import argparse
import heapq
from pathlib import Path

import generate_dispatch_invariant as base

HERE = Path(__file__).resolve().parent


def render():
    table = base.rows()
    dist = {284: 0}
    pending = [(0, 284)]
    while pending:
        current, state = heapq.heappop(pending)
        if current != dist[state]:
            continue
        for read in (0, 1):
            write, move, target, event = table[state, read]
            if write != read or move != "R" or event:
                continue
            candidate = current + int(read == 0)
            if candidate < dist.get(target, 1000):
                dist[target] = candidate
                heapq.heappush(pending, (candidate, target))
    ranks = [min(dist.get(i, 0), 3) for i in range(285)]
    lines = ",\n".join("  " + ", ".join(str(x) for x in ranks[i:i+15])
                         for i in range(0, len(ranks), 15))
    return """import Shared.PNP.Record285.ControlSafe

/-! Generated zero-count lower bounds, separately checked in Lean. -/
namespace Shared.PNP.Record285.ControlBreakRankData

def rankData : Array Nat := #[
""" + lines + """
]

end Shared.PNP.Record285.ControlBreakRankData
"""


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--check", action="store_true")
    args = parser.parse_args()
    target = HERE / "ControlBreakRankData.lean"
    content = render()
    if args.check:
        if target.read_text() != content:
            raise SystemExit("break ranks differ from deterministic extraction")
        print("break ranks match; Lean checks their meaning")
    else:
        target.write_text(content)
        print("wrote", target)


if __name__ == "__main__":
    main()
