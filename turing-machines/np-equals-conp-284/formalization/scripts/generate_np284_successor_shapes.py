#!/usr/bin/env python3
"""Generate bounded Lean checks for the 185 producer graph-state shapes."""
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
OUT = ROOT / 'Shared' / 'Beeping' / 'NPcoNP'

for number, lo in enumerate(range(0, 185, 10)):
    count = min(10, 185 - lo)
    name = f'Grammar284SuccessorShapeShard{number:02d}'
    content = f'''import Shared.Beeping.NPcoNP.Grammar284SuccessorShapeBase

/-! Generated bounded producer-successor shape check: states {lo}–{lo + count - 1}. -/
namespace Shared.Beeping.NPcoNP.{name}
open Shared.Beeping.NPcoNP.Grammar284SuccessorShapeBase
set_option maxRecDepth 131072
set_option maxHeartbeats 100000000

theorem checked : rangeCheck {lo} {count} = true := by
  decide
end Shared.Beeping.NPcoNP.{name}
'''
    (OUT / f'{name}.lean').write_text(content, encoding='utf-8')
