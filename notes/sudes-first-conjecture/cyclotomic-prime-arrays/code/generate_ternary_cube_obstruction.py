#!/usr/bin/env python3
"""Create a small explicit proof tree for the full signed 3-cube obstruction.

Author: /root/normalization. This search is independent of the prime-array
producer. The companion verifier checks every forcing step and branch; it
does not trust the search result or its branching heuristic.
"""
import argparse
from itertools import product
import json
from pathlib import Path


def lines():
    out = set()
    for direction in product((-1, 0, 1), repeat=3):
        nonzero = [d for d in direction if d]
        if not nonzero or nonzero[0] != 1:
            continue
        fixed_axes = [j for j, d in enumerate(direction) if d == 0]
        for fixed_values in product(range(3), repeat=len(fixed_axes)):
            start = [0 if d >= 0 else 2 for d in direction]
            for j, value in zip(fixed_axes, fixed_values):
                start[j] = value
            cells = []
            for t in range(3):
                p = [start[j] + t * direction[j] for j in range(3)]
                cells.append(9 * p[0] + 3 * p[1] + p[2])
            out.add(tuple(sorted(cells)))
    assert len(out) == 49
    return sorted(out)


def build_proof():
    required = lines()
    incidence = [[] for _ in range(27)]
    for j, line in enumerate(required):
        for cell in line:
            incidence[cell].append(j)

    def search(state):
        state = list(state)
        forces = []
        while True:
            changed = False
            for line in required:
                values = [state[x] for x in line]
                if values == [0, 0, 0] or values == [1, 1, 1]:
                    return {"forces": forces, "conflict": list(line)}
                unknown = [x for x in line if state[x] == -1]
                if len(unknown) == 1:
                    known = [state[x] for x in line if state[x] != -1]
                    if known[0] == known[1]:
                        cell, color = unknown[0], 1 - known[0]
                        state[cell] = color
                        forces.append({"line": list(line), "cell": cell, "color": color})
                        changed = True
            if not changed:
                break
        unknown = [x for x in range(27) if state[x] == -1]
        if not unknown:
            raise RuntimeError("A complete valid coloring exists: " + repr(state))
        cell = max(unknown, key=lambda x: sum(
            2 ** sum(state[y] != -1 for y in required[j]) for j in incidence[x]))
        children = []
        for color in (0, 1):
            child_state = state[:]
            child_state[cell] = color
            children.append(search(child_state))
        return {"forces": forces, "branch": cell, "children": children}

    state = [-1] * 27
    state[13] = 0
    return {"format": "full-signed-cube3-two-colour-unsat-v1",
            "side": 3, "dimension": 3, "colors": 2,
            "fixed_center": {"cell": 13, "color": 0},
            "root": search(state)}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("output", type=Path)
    args = parser.parse_args()
    proof = build_proof()
    args.output.write_text(json.dumps(proof, indent=2) + "\n")
    print(json.dumps({"status": "proof-generated", "output": str(args.output)}))


if __name__ == "__main__":
    main()
