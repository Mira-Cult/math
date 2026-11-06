"""Generate candidate numbering from generated full-row data.

This untrusted script reads the generated Lean row source. Lean must prove its
own `number` returns the candidate; the file is not a producer binding.
"""
import argparse
import re
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROW = re.compile(r'^  ⟨"([^"]+)", \[[0-9, ]*\]⟩,?$')


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--input", type=Path, default=HERE / "Grammar284FullRows.lean")
    parser.add_argument("--output", type=Path, default=HERE / "Grammar284NumberingData.lean")
    args = parser.parse_args()
    lines = args.input.read_text(encoding="utf-8").splitlines()
    ops = [m.group(1) for line in lines if (m := ROW.fullmatch(line))]
    if len(ops) != 279:
        raise ValueError(f"expected 279 parsed rows, got {len(ops)}")
    mapping, kept = [], []
    for i, op in enumerate(ops):
        if op == "jump":
            mapping.append("none")
        else:
            mapping.append(f"some {len(kept)}")
            kept.append(i)
    output = [
        "import Shared.Beeping.NPcoNP.Grammar284FullRows", "",
        "/-! Generated candidate numbering; equality to `number` requires",
        "a separate kernel proof. -/", "",
        "namespace Shared.Beeping.NPcoNP.Grammar284", "",
        "def producerNumbering : Numbering := ⟨", "  #[",
    ]
    output += [f"    {v}," for v in mapping]
    output[-1] = output[-1].removesuffix(",")
    output += ["  ],", "  #["]
    output += [f"    {v}," for v in kept]
    output[-1] = output[-1].removesuffix(",")
    output += ["  ]⟩", "", "end Shared.Beeping.NPcoNP.Grammar284", ""]
    args.output.write_text("\n".join(output), encoding="utf-8")


if __name__ == "__main__":
    main()
