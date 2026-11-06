"""Generate kernel-decision shards for the literal parent290 mask data.

Generated proofs certify only the Lean literal program and mask data. They do
not prove the producer-byte, graph-extraction, coalescing, or tape bindings.
The destination is explicit so generation can first be checked in a temporary
directory without overwriting a collaborator's files.
"""
import argparse
import hashlib
from pathlib import Path

HERE = Path(__file__).resolve().parent
DATA = HERE / "Parent290MaskData.lean"
DATA_SHA256 = "32712f6a0188f4a5b5f109fb4d7a843c39def17345307cda00c952a3f49ccebf"
ROWS = 185
WIDTH = 10


def shard(index: int) -> str:
    low = WIDTH * index
    high = min(low + WIDTH, ROWS)
    namespace = f"Parent290MaskShard{index:02d}"
    lines = [
        "import Shared.Beeping.NPcoNP.MaskInvariantRowCheck",
        "import Shared.Beeping.NPcoNP.Parent290MaskData", "",
        f"/-! Kernel-checked mask-closure facts for rows {low}–{high - 1} of the generated literal",
        "program. These do not establish the producer grammar or table bindings. -/",
        f"namespace Shared.Beeping.NPcoNP.{namespace}",
        "open MaskInvariant Parent290MaskData", "set_option maxRecDepth 8192",
        "set_option maxHeartbeats 0", "",
    ]
    lines.extend(
        f"theorem row{i:03d} : rowCheck program masks ({i} : Fin {ROWS}) = true := by decide"
        for i in range(low, high)
    )
    lines.extend(["", f"end Shared.Beeping.NPcoNP.{namespace}", ""])
    return "\n".join(lines)


def coverage() -> str:
    count = (ROWS + WIDTH - 1) // WIDTH
    lines = [f"import Shared.Beeping.NPcoNP.Parent290MaskShard{i:02d}" for i in range(count)]
    lines.extend([
        "", "/-! Coverage for the generated literal register program only. Source",
        "grammar, administrative contraction, and physical coalescence remain",
        "separate obligations. -/",
        "namespace Shared.Beeping.NPcoNP.Parent290MaskCoverage",
        "open MaskInvariant Parent290MaskData", "set_option maxRecDepth 8192",
        "set_option maxHeartbeats 0", "",
        "theorem allRows (s : Fin 185) : rowCheck program masks s = true := by",
        "  fin_cases s",
    ])
    lines.extend(f"  · exact Parent290MaskShard{i // WIDTH:02d}.row{i:03d}" for i in range(ROWS))
    lines.extend([
        "", "theorem closed : Closed program masks :=",
        "  closed_of_all_rowCheck program masks allRows", "",
        "end Shared.Beeping.NPcoNP.Parent290MaskCoverage", "",
    ])
    return "\n".join(lines)


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output-dir", type=Path, required=True)
    args = parser.parse_args()
    digest = hashlib.sha256(DATA.read_bytes()).hexdigest()
    if digest != DATA_SHA256:
        raise ValueError(f"unexpected data SHA-256: {digest}")
    args.output_dir.mkdir(parents=True, exist_ok=True)
    names = []
    for i in range((ROWS + WIDTH - 1) // WIDTH):
        name = f"Parent290MaskShard{i:02d}.lean"
        (args.output_dir / name).write_text(shard(i), encoding="utf-8")
        names.append(name)
    name = "Parent290MaskCoverage.lean"
    (args.output_dir / name).write_text(coverage(), encoding="utf-8")
    names.append(name)
    print(f"data_sha256={digest} files={len(names)} rows={ROWS} width={WIDTH}")


if __name__ == "__main__":
    main()
