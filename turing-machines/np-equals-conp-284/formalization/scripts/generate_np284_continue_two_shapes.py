#!/usr/bin/env python3
"""Regenerate bounded Lean checks for the 60 continue-two grammar leaves."""
from pathlib import Path

root = Path(__file__).resolve().parents[1] / "Shared/Beeping/NPcoNP"
for shard in range(6):
    name = f"Grammar284ContinueTwoShapeShard{shard:02d}"
    (root / f"{name}.lean").write_text(f"""import Shared.Beeping.NPcoNP.Grammar284ContinueTwoShapeBase
namespace Shared.Beeping.NPcoNP.{name}
open Shared.Beeping.NPcoNP.Grammar284ContinueTwoShapeBase
set_option maxRecDepth 131072
set_option maxHeartbeats 200000000
theorem checked : rangeCheck {10 * shard} 10 = true := by decide
end Shared.Beeping.NPcoNP.{name}
""")
