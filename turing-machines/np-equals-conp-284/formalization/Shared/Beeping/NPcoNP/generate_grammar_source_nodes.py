"""Generate kernel-checked node/tail equations for the pinned grammar AST.

Every generated statement is checked by Lean `rfl`. This generator is not a
proof that the source is JSON or that the rows compose; those obligations are
handled by separate formal modules. Generation requires an explicit output
directory, so a reproduction check does not overwrite existing source.
"""

import argparse
import hashlib
from pathlib import Path

HERE = Path(__file__).resolve().parent
PINS = {
    "Grammar284Data.lean": "ca5e78885fbb70779161a169aeba52877e77d86fc9aacf78ac3d7c18c27286cf",
    "Grammar284SourceTails.lean": "f3c221208c9ab019fbdb382c8691bd46ce16828fc34c387346b5757f8ea5f2db",
    "Grammar284SourceRender.lean": "e4c21d6098e395945f5a4cd5944195a078b0921424a8c49684897e62a2fb188f",
}
ROWS = 160
WIDTH = 10


def shard(index: int) -> str:
    low, high = index * WIDTH, min((index + 1) * WIDTH, ROWS)
    ns = f"SourceNodeShard{index:02d}"
    lines = [
        "import Shared.Beeping.NPcoNP.Grammar284SourceTails",
        "import Shared.Beeping.NPcoNP.Grammar284SourceRender",
        "",
        f"/-! Kernel-checked source-tail equations for node indices {low}–{high - 1}.",
        "These local equations require a separate full-file composition theorem. -/",
        f"namespace Shared.Beeping.NPcoNP.Grammar284.{ns}",
        "open Shared.Beeping.NPcoNP.Grammar284.SourceTails",
        "open Shared.Beeping.NPcoNP.Grammar284.SourceRender",
        "set_option maxRecDepth 100000",
        "set_option maxHeartbeats 0",
        "",
    ]
    for i in range(low, high):
        delimiter = r'",\n"' if i < ROWS - 1 else r'"\n"'
        lines.extend([
            f"theorem row{i:03d} :",
            f"    tail{i + 1} = node producerGrammar.nodes[{i}]! ++ {delimiter}.toList ++ tail{i + 2} := by rfl",
        ])
    lines.extend(["", f"end Shared.Beeping.NPcoNP.Grammar284.{ns}", ""])
    return "\n".join(lines)


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output-dir", type=Path, required=True)
    args = parser.parse_args()
    for name, expected in PINS.items():
        actual = hashlib.sha256((HERE / name).read_bytes()).hexdigest()
        if actual != expected:
            raise ValueError(f"unexpected {name} SHA-256: {actual}")
    args.output_dir.mkdir(parents=True, exist_ok=True)
    for index in range((ROWS + WIDTH - 1) // WIDTH):
        name = f"GrammarSourceNodeShard{index:02d}.lean"
        (args.output_dir / name).write_text(shard(index), encoding="utf-8")
    print(f"shards={(ROWS + WIDTH - 1) // WIDTH} rows={ROWS} width={WIDTH}")


if __name__ == "__main__":
    main()
