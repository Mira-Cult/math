"""Generate small kernel-checked newline-freeness proofs for table lines.

These shards check the supplied Lean line data, not its correspondence to
the input file. The latter is established separately by SourceJoin.
"""
import argparse
from pathlib import Path


def shard(index: int) -> str:
    low, high = 10 * index, min(10 * (index + 1), 29)
    lines = [
        "import Shared.Beeping.NPcoNP.Table284LineData", "",
        "/-! Kernel checks for newline-free data lines in one finite chunk. -/",
        "namespace Shared.Beeping.NPcoNP.Table284SourceLines",
        "open Shared.Beeping.NPcoNP.Table284LineData",
        "set_option maxRecDepth 8192", "set_option maxHeartbeats 0", "",
    ]
    lines += [
        f"theorem clean{i:02d} : lines{i:02d}.all (fun line => decide ('\\n' ∉ line)) = true := by decide"
        for i in range(low, high)
    ]
    lines += ["", "end Shared.Beeping.NPcoNP.Table284SourceLines", ""]
    return "\n".join(lines)


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output-dir", type=Path, required=True)
    args = parser.parse_args()
    args.output_dir.mkdir(parents=True, exist_ok=True)
    for index in range(3):
        (args.output_dir / f"Table284CleanShard{index:02d}.lean").write_text(
            shard(index), encoding="utf-8"
        )


if __name__ == "__main__":
    main()
