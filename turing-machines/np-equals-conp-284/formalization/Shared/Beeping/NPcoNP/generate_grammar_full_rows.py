"""Generate candidate ordered full-graph rows from the pinned grammar JSON.

This generator is untrusted: Lean must separately verify each generated row
against its own expansion and fullRow interpreter. It intentionally rejects
malformed administrative suffixes rather than treating this script as a
specification of arbitrary Python parser inputs.
"""
import argparse
import json
from pathlib import Path

HERE = Path(__file__).resolve().parent


def generate():
    grammar = json.loads((HERE / "Inputs" / "parent290-grammar.json").read_text())
    starts, leaves = {}, []

    def visit(leaf, path, ancestors):
        if path in starts:
            raise ValueError("duplicate expansion path")
        starts[path] = len(leaves)
        if set(leaf) == {"op"}:
            leaves.append((path, leaf["op"]))
        elif set(leaf) == {"node"}:
            i = leaf["node"]
            if i in ancestors:
                raise ValueError("cyclic grammar")
            a, b = grammar["nodes"][i]
            visit(a, path + (False,), ancestors | {i})
            visit(b, path + (True,), ancestors | {i})
        else:
            raise ValueError("invalid leaf")

    visit({"node": grammar["root"]}, (True, True, False), set())

    def resolve(path):
        return 0 if path == (True, True) or path[:3] == (True, True, True) else starts[path]

    def successor(path, skip):
        candidates = [i for i in range(len(path) - 1, 1, -1) if not path[i]]
        return resolve(path[:candidates[skip]] + (True,))

    def restart(path, skip):
        candidates = [i for i in range(len(path) - 1, 0, -1) if path[i]]
        return resolve(path[:candidates[skip] + 1])

    rows = []
    for path, op in leaves:
        if op in ("_break.1", "_break.2"):
            rows.append(("jump", [successor(path, int(op[-1]))]))
        elif op in ("_continue.1", "_continue.2"):
            rows.append(("jump", [restart(path, int(op[-1]))]))
        elif op.endswith(".decnz"):
            rows.append((op, [successor(path, 0), successor(path, 1)]))
        else:
            rows.append((op, [successor(path, 0)]))

    lines = [
        "import Shared.Beeping.NPcoNP.GrammarGraph284", "",
        "/-! Untrusted generated candidate full rows. Their identity with the",
        "Lean grammar interpreter requires an independent kernel certificate. -/", "",
        "namespace Shared.Beeping.NPcoNP.Grammar284", "",
        "def producerFullRows : Array Row := #[",
    ]
    for op, dst in rows:
        if not op.isascii():
            raise ValueError("expected ASCII operations")
        lines.append(f"  ⟨{json.dumps(op)}, [{', '.join(map(str, dst))}]⟩,")
    lines[-1] = lines[-1].removesuffix(",")
    lines.extend(["]", "", "end Shared.Beeping.NPcoNP.Grammar284", ""])
    return "\n".join(lines)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, default=HERE / "Grammar284FullRows.lean")
    args = parser.parse_args()
    args.output.write_text(generate(), encoding="utf-8")


if __name__ == "__main__":
    main()
