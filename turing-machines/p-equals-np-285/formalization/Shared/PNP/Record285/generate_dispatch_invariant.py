#!/usr/bin/env python3
"""Generate finite dispatcher reachability masks; Lean checks every edge.

The generator is untrusted. Soundness rests on the checked seed, closure, and
root-bound obligations; the masks are not assumed minimal.
"""
from collections import defaultdict, deque
from pathlib import Path
import argparse

HERE = Path(__file__).resolve().parent
TERMINALS = [76, 78, 90, 92, 94, 96, 98, 100, 102, 104, 80, 82, 84, 86, 88]


def rows():
    result = {}
    for line in (HERE / "events.tm").read_text().splitlines():
        if line.startswith("#") or not line.strip():
            continue
        state, read, write, move, nxt, flag = line.split()
        result[int(state), int(read)] = (int(write), move, int(nxt), int(flag))
    if len(result) != 570:
        raise ValueError("expected exactly 570 transition rows")
    return result


def masks(table):
    pending = deque([284])
    forward = {284}
    incoming = defaultdict(list)
    while pending:
        q = pending.popleft()
        for bit in (0, 1):
            write, move, nxt, flag = table[q, bit]
            if write == bit and move == "R" and flag == 0:
                incoming[nxt].append((q, bit))
                if nxt not in forward:
                    forward.add(nxt)
                    pending.append(nxt)
    if not set(TERMINALS) <= forward:
        raise ValueError("increment terminal not forward reachable")
    back = {(q, 0) for q in TERMINALS}
    pending = deque(sorted(back))
    while pending:
        q, zeros = pending.popleft()
        for prev, bit in incoming[q]:
            if bit == 0 and zeros == 4:
                raise ValueError("a reachable reverse path contains five zeros")
            next_zeros = 0 if bit else zeros + 1
            pair = (prev, next_zeros)
            if pair not in back:
                back.add(pair)
                pending.append(pair)
    fwd = [q in forward for q in range(285)]
    bwd = [sum(1 << d for state, d in back if state == q) for q in range(285)]
    return fwd, bwd


def render():
    fwd, bwd = masks(rows())
    line = lambda xs: ",\n".join("  " + ", ".join(xs[i:i+15]) for i in range(0, len(xs), 15))
    return """import Shared.PNP.Record285.GenericDispatchBridge

/-! Generated finite masks. Their soundness comes from the separate checked
closure and seed obligations, not from the generator. -/
namespace Shared.PNP.Record285.DispatcherInvariantData

def forwardData : Array Bool := #[
""" + line([str(x).lower() for x in fwd]) + """
]

def backwardData : Array Nat := #[
""" + line([str(x) for x in bwd]) + """
]

end Shared.PNP.Record285.DispatcherInvariantData
"""


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--check", action="store_true")
    args = parser.parse_args()
    target = HERE / "DispatcherInvariantData.lean"
    content = render()
    if args.check:
        if target.read_text() != content:
            raise SystemExit("dispatcher mask source differs from regenerated masks")
        print("dispatcher masks match deterministic extraction; Lean checks their meaning")
    else:
        target.write_text(content)
        print("wrote", target)


if __name__ == "__main__":
    main()
