#!/usr/bin/env python3
"""Check the checkpoint compositions conditional on four interval counts.

This derives a temporary Lean file from the current canonical definitions and
proof bodies. It does not check the generated certificates or build the actual
checkpoint modules. From the Lean root, after installing the pinned Lake,
Lean, and mathlib dependencies, run: python3 scripts/check_twin_composition.py.
"""

import hashlib
import os
from pathlib import Path
import re
import subprocess
import tempfile


ROOT = Path(__file__).resolve().parent.parent
SOURCE = ROOT / "Sude"


def extract(filename: str, start: str, end: str) -> str:
    text = (SOURCE / filename).read_text(encoding="utf-8")
    if text.count(start) != 1 or text.count(end) != 1:
        raise ValueError(f"expected unique source boundaries in {filename}")
    begin, finish = text.index(start), text.index(end)
    if begin >= finish:
        raise ValueError(f"reversed source boundaries in {filename}")
    return text[begin:finish]


def replace_once(text: str, old: str, new: str) -> str:
    if text.count(old) != 1:
        raise ValueError(f"expected exactly one occurrence of {old!r}")
    return text.replace(old, new, 1)


def source() -> str:
    pieces = [
        extract("TwinSegmentSieve.lean", "def twinPrimeSegment ", "\n/-- Mark one extra"),
        extract("FiniteTwinSeed.lean", "def finiteTwinSeeds ", "\n/-- The finite twin-prime set"),
        extract("TwinSegmentScan.lean", "theorem twinPrimeSegment_union ", "\n/-- Count each segment"),
        extract("FiniteTwinFlexible.lean", "theorem combineTwinPrimeSegments ", "\nend\nend Sude"),
    ]
    counts = """(lowCount : (twinPrimeSegment 45 12582957).card = 71866)
    (midCount : (twinPrimeSegment 538968109 541065261).card = 6806)
    (highCount : (twinPrimeSegment 1073709055 1073741823).card = 90)"""
    seven = extract(
        "FiniteTwinCheckpointSeven.lean", "theorem finiteTwinSeeds_at_least_78762",
        "\nend\nend Sude",
    )
    seven = replace_once(seven, " : 78762 ≤ finiteTwinSeeds.card", f" {counts} : 78762 ≤ finiteTwinSeeds.card")
    seven = replace_once(seven, ":= finiteTwinFirstSixSegments", ":= lowCount")
    seven = replace_once(seven, ":= GeneratedTwinScan.S257All.total", ":= midCount")
    seven = replace_once(seven, ":= finiteTwinHighActive16384_mathematical", ":= highCount")

    eight = extract(
        "FiniteTwinCheckpointEight.lean", "theorem finiteTwinSeeds_at_least_85524",
        "\nend\nend Sude",
    )
    counts8 = counts + "\n    (nextCount : (twinPrimeSegment 541065261 543162413).card = 6762)"
    eight = replace_once(eight, " : 85524 ≤ finiteTwinSeeds.card", f" {counts8} : 85524 ≤ finiteTwinSeeds.card")
    eight = replace_once(eight, ":= finiteTwinFirstSixSegments", ":= lowCount")
    eight = replace_once(
        eight, "GeneratedTwinScan.S257All.total GeneratedTwinScan.S258All.total",
        "midCount nextCount",
    )
    eight = replace_once(eight, ":= finiteTwinHighActive16384_mathematical", ":= highCount")
    pieces.extend([seven, eight])
    for piece in pieces:
        if re.search(r"\b(?:sorry|admit|axiom|native_decide|unsafe|implemented_by)\b", piece):
            raise ValueError("disallowed declaration or proof shortcut in extracted source")
    return (
        "import Mathlib\n\nnamespace Sude\nnoncomputable section\n\n"
        + "\n".join(pieces)
        + "\nend\nend Sude\n"
        + "#print axioms Sude.finiteTwinSeeds_at_least_78762\n"
        + "#print axioms Sude.finiteTwinSeeds_at_least_85524\n"
    )


def main() -> None:
    lean_source = source()
    digest = hashlib.sha256(lean_source.encode("utf-8")).hexdigest()
    expected = "".join(
        f"'Sude.finiteTwinSeeds_at_least_{bound}' depends on axioms: "
        "[propext, Classical.choice, Quot.sound]\n"
        for bound in (78762, 85524)
    )
    with tempfile.TemporaryDirectory(prefix="sude-twin-composition-") as temp:
        target = Path(temp) / "Composition.lean"
        target.write_text(lean_source, encoding="utf-8")
        env = os.environ.copy()
        env["LEAN_NUM_THREADS"] = "1"
        result = subprocess.run(
            ["lake", "env", "lean", str(target)], cwd=ROOT, env=env,
            text=True, capture_output=True, check=False,
        )
        if result.returncode != 0 or result.stdout != expected:
            raise RuntimeError(
                f"Lean check or axiom audit failed (exit {result.returncode}):\n"
                f"{result.stdout}{result.stderr}"
            )
        if result.stderr:
            raise RuntimeError(f"unexpected Lean diagnostic:\n{result.stderr}")
    print(f"Conditional composition checked; generated Lean SHA-256: {digest}")
    print("Count hypotheses: 71866, 6806, 90; additionally 6762 for the stronger bound.")
    print("Axioms: propext, Classical.choice, Quot.sound. Certificate counts were not checked.")


if __name__ == "__main__":
    main()
