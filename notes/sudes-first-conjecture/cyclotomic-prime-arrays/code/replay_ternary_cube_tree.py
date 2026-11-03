#!/usr/bin/env python3
"""Exactly verify an explicit exhaustive two-colour obstruction proof tree.

Author: /root/normalization. Standard library only. No imports from the proof
generator, prime-array producer, or prime-array checkers. Every line is
reconstructed from its endpoint coordinates; every propagation and both
branches are verified. This is an exact finite proof checker, not a report
that a heuristic failed to find a coloring. The generator and checker share
an author; no independent authorship review is claimed by this program.
"""
import argparse
import copy
from itertools import combinations, product
import json
from pathlib import Path


class InvalidProof(ValueError):
    pass


def require(condition, message):
    if not condition:
        raise InvalidProof(message)


def full_lines():
    """Every full line joins two opposite corners of a coordinate face."""
    points = list(product(range(3), repeat=3))
    labels = {p: i for i, p in enumerate(points)}
    result = set()
    for a, b in combinations(points, 2):
        delta = tuple(b[j] - a[j] for j in range(3))
        if all(d in (-2, 0, 2) for d in delta):
            midpoint = tuple((a[j] + b[j]) // 2 for j in range(3))
            result.add(tuple(sorted((labels[a], labels[midpoint], labels[b]))))
    require(len(result) == 49, "internal full-line count failed")
    return result


def check(data):
    require(data.get("format") == "full-signed-cube3-two-colour-unsat-v1",
            "wrong proof format")
    require((data.get("side"), data.get("dimension"), data.get("colors")) == (3, 3, 2),
            "wrong finite problem")
    require(data.get("fixed_center") == {"cell": 13, "color": 0},
            "only center-color symmetry is licensed")
    required = full_lines()
    stats = {"nodes": 0, "branches": 0, "conflicts": 0, "forced_assignments": 0,
             "maximum_depth": 0, "full_lines": len(required)}

    def line_key(line):
        require(isinstance(line, list) and len(line) == 3 and
                all(type(x) is int for x in line), "malformed line")
        result = tuple(sorted(line))
        require(result in required, "a proof step uses a nonrequired line")
        return result

    def verify(node, state, depth):
        require(isinstance(node, dict), "malformed proof node")
        stats["nodes"] += 1
        stats["maximum_depth"] = max(stats["maximum_depth"], depth)
        state = list(state)
        forces = node.get("forces")
        require(isinstance(forces, list), "missing force list")
        for force in forces:
            require(isinstance(force, dict), "malformed forced assignment")
            line = line_key(force.get("line"))
            cell, color = force.get("cell"), force.get("color")
            require(type(cell) is int and cell in line and state[cell] == -1,
                    "forced cell is already assigned or not in its line")
            require(type(color) is int and color in (0, 1), "invalid forced color")
            others = [state[x] for x in line if x != cell]
            require(others == [1-color, 1-color], "forced color is not logically necessary")
            state[cell] = color
            stats["forced_assignments"] += 1
        if "conflict" in node:
            require(set(node) == {"forces", "conflict"}, "conflict node has extra operations")
            line = line_key(node["conflict"])
            values = [state[x] for x in line]
            require(values == [0, 0, 0] or values == [1, 1, 1],
                    "claimed leaf is not a monochromatic line")
            stats["conflicts"] += 1
            return
        require(set(node) == {"forces", "branch", "children"}, "malformed branch node")
        cell, children = node["branch"], node["children"]
        require(type(cell) is int and 0 <= cell < 27 and state[cell] == -1,
                "branch cell is not a free cell")
        require(isinstance(children, list) and len(children) == 2,
                "both colors must be covered")
        stats["branches"] += 1
        for color, child in enumerate(children):
            child_state = state[:]
            child_state[cell] = color
            verify(child, child_state, depth+1)

    initial = [-1] * 27
    initial[13] = 0
    verify(data.get("root"), initial, 0)
    require(stats["conflicts"] == stats["branches"] + 1, "proof is not a full binary tree")
    # Every two-coloring can be globally exchanged so that its center is 0.
    # Every forced assignment is necessary, both colors are checked at each
    # branch, and every leaf contradicts a required line. Therefore none exists.
    return {"status": "verified-unsatisfiable", **stats}


def negative_controls(data):
    altered = copy.deepcopy(data)
    altered["root"]["children"].pop()
    try:
        check(altered)
    except InvalidProof:
        pass
    else:
        raise InvalidProof("missing-branch mutation accepted")
    altered = copy.deepcopy(data)
    node = altered["root"]
    while "children" in node:
        node = node["children"][0]
    node["conflict"] = [0, 1, 13]
    try:
        check(altered)
    except InvalidProof:
        pass
    else:
        raise InvalidProof("false-conflict mutation accepted")
    return 2


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("proof", type=Path)
    parser.add_argument("--negative-controls", action="store_true")
    args = parser.parse_args()
    data = json.loads(args.proof.read_text())
    result = check(data)
    if args.negative_controls:
        result["negative_controls_rejected"] = negative_controls(data)
    print(json.dumps(result, sort_keys=True))


if __name__ == "__main__":
    main()
