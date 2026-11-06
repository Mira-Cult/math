#!/usr/bin/env python3
"""Reconstruct a candidate graph literal from the preserved grammar JSON.

This is an independent host-language reconstruction, not a proof of identity
with the producer algorithm or the Lean `coreGraph` interpretation. The Lean
comparison certificate checks the resulting literal separately.
"""
import argparse
import json
from pathlib import Path


def reconstruct(grammar):
    starts, leaves = {}, []

    def visit(value, path, ancestors):
        starts[path] = len(leaves)
        if "node" in value:
            index = value["node"]
            if index in ancestors:
                raise ValueError("cyclic grammar")
            left, right = grammar["nodes"][index]
            visit(left, path + (False,), ancestors | {index})
            visit(right, path + (True,), ancestors | {index})
        elif set(value) == {"op"}:
            leaves.append((path, value["op"]))
        else:
            raise ValueError("malformed leaf")

    visit({"node": grammar["root"]}, (True, True, False), set())

    def resolve(path):
        return 0 if path == (True, True) or path[:3] == (True, True, True) else starts[path]

    def successor(path, skip):
        for pos in range(len(path) - 1, 1, -1):
            if not path[pos]:
                if skip == 0:
                    return resolve(path[:pos] + (True,))
                skip -= 1
        raise ValueError("no successor")

    def restart(path, skip):
        for pos in range(len(path) - 1, 0, -1):
            if path[pos]:
                if skip == 0:
                    return resolve(path[:pos + 1])
                skip -= 1
        raise ValueError("no restart")

    full = []
    for path, op in leaves:
        if op.startswith("_break."):
            full.append(("jump", successor(path, int(op.split(".")[1]))))
        elif op.startswith("_continue."):
            full.append(("jump", restart(path, int(op.split(".")[1]))))
        elif op.endswith(".decnz"):
            full.append((op, successor(path, 0), successor(path, 1)))
        else:
            full.append((op, successor(path, 0)))
    retained = [i for i, row in enumerate(full) if row[0] != "jump"]
    numbering = {old: new for new, old in enumerate(retained)}

    def target(index):
        seen = set()
        while full[index][0] == "jump":
            if index in seen:
                raise ValueError("administrative cycle")
            seen.add(index)
            index = full[index][1]
        return numbering[index]

    for i in range(len(full)):
        target(i)
    return target(0), [(full[i][0], *(target(j) for j in full[i][1:])) for i in retained]


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--input", default="Shared/Beeping/NPcoNP/Inputs/parent290-grammar.json")
    parser.add_argument("--output", default="Shared/Beeping/NPcoNP/GraphCandidate284Data.lean")
    args = parser.parse_args()
    entry, rows = reconstruct(json.loads(Path(args.input).read_text()))
    assert entry == 0 and len(rows) == 185
    lines = ["import Shared.Beeping.NPcoNP.GrammarGraph284", "", 
             "/-! Generated diagnostic graph literal; correspondence to the original",
             "JSON, the Lean grammar interpreter and producer's algorithm is unproved. -/", "",
             "namespace Shared.Beeping.NPcoNP.GraphCandidate284", "open Shared.Beeping.NPcoNP.Grammar284", "",
             "def graph : Graph := ⟨0, #["]
    for op, *targets in rows:
        assert all(32 <= ord(c) < 127 for c in op)
        lines.append("  ⟨" + json.dumps(op) + ", [" + ", ".join(map(str, targets)) + "]⟩,")
    lines[-1] = lines[-1].removesuffix(",")
    lines += ["]⟩", "", "end Shared.Beeping.NPcoNP.GraphCandidate284", ""]
    Path(args.output).write_text("\n".join(lines))


if __name__ == "__main__":
    main()
