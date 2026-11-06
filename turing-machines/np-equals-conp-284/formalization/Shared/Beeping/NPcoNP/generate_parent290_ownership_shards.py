"""Generate kernel-checked ownership shards for literal parent290 data.

The output concerns the generated Lean program, masks and literal suffix map;
it does not prove any external source, graph, coalescing, or tape binding.
"""
import argparse
import hashlib
from pathlib import Path

HERE = Path(__file__).resolve().parent
PINS = {
    "Parent290MaskData.lean": "32712f6a0188f4a5b5f109fb4d7a843c39def17345307cda00c952a3f49ccebf",
    "Coalescing284Map.lean": "d500c69ed5c579410339aa8d11c02af0ef9cba50eb9af638c3216fb25414263f",
}
ROWS, WIDTH = 185, 10


def shard(k: int) -> str:
    lo, hi = k * WIDTH, min((k + 1) * WIDTH, ROWS)
    name = f"Parent290OwnershipShard{k:02d}"
    lines = [
        "import Shared.Beeping.NPcoNP.CoalescingMaskCheck",
        "import Shared.Beeping.NPcoNP.Coalescing284Map",
        "import Shared.Beeping.NPcoNP.Parent290MaskData", "",
        f"/-! Kernel ownership checks for generated program rows {lo}–{hi-1}.",
        "External source and physical bindings remain unproved. -/",
        f"namespace Shared.Beeping.NPcoNP.{name}",
        "open CoalescingAlgebra Coalescing284Map Parent290MaskData",
        "set_option maxRecDepth 8192", "set_option maxHeartbeats 0", "",
    ]
    lines.extend(
        f"theorem row{i:03d} : maskAccessCheck logicalToSuffix (masks {i}) program.code[{i}].action = true := by decide"
        for i in range(lo, hi)
    )
    lines.extend(["", f"end Shared.Beeping.NPcoNP.{name}", ""])
    return "\n".join(lines)


def coverage() -> str:
    count = (ROWS + WIDTH - 1) // WIDTH
    lines = [f"import Shared.Beeping.NPcoNP.Parent290OwnershipShard{k:02d}" for k in range(count)]
    lines += [
        "", "/-! Finite ownership coverage for the generated literal program.",
        "Producer, coalesced graph and physical machine bindings remain open. -/",
        "namespace Shared.Beeping.NPcoNP.Parent290OwnershipCoverage",
        "open CoalescingAlgebra Coalescing284Map Parent290MaskData",
        "set_option maxRecDepth 8192", "set_option maxHeartbeats 0", "",
        "theorem allChecks (s : Fin 185) :",
        "    maskAccessCheck logicalToSuffix (masks s) program.code[s].action = true := by",
        "  fin_cases s",
    ]
    lines.extend(f"  · exact Parent290OwnershipShard{i // WIDTH:02d}.row{i:03d}" for i in range(ROWS))
    lines += [
        "", "theorem allOwners (s : Fin 185) :",
        "    MaskAccessOK logicalToSuffix (masks s) program.code[s].action :=",
        "  maskAccessOK_of_check logicalToSuffix (masks s) program.code[s].action (allChecks s)",
        "", "end Shared.Beeping.NPcoNP.Parent290OwnershipCoverage", "",
    ]
    return "\n".join(lines)


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output-dir", required=True, type=Path)
    args = parser.parse_args()
    for name, expected in PINS.items():
        actual = hashlib.sha256((HERE / name).read_bytes()).hexdigest()
        if actual != expected:
            raise ValueError(f"unexpected {name} SHA-256: {actual}")
    args.output_dir.mkdir(parents=True, exist_ok=True)
    for k in range((ROWS + WIDTH - 1) // WIDTH):
        (args.output_dir / f"Parent290OwnershipShard{k:02d}.lean").write_text(shard(k), encoding="utf-8")
    (args.output_dir / "Parent290OwnershipCoverage.lean").write_text(coverage(), encoding="utf-8")
    print(f"files={(ROWS + WIDTH - 1) // WIDTH + 1} rows={ROWS} width={WIDTH}")


if __name__ == "__main__":
    main()
