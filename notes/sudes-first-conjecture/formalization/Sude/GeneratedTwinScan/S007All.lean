import Sude.GeneratedTwinScan.S007C15

/-! Combined kernel-checked FT source segment. -/
namespace Sude.GeneratedTwinScan
namespace S007All

theorem join_0_0 : (twinPrimeSegment 14680109 14942253).card = 1256 := by
  simpa using combineTwinPrimeSegments (by decide : 14680109 ≤ 14811181)
    (by decide : 14811181 ≤ 14942253) S007C00.total S007C01.total

theorem join_0_1 : (twinPrimeSegment 14942253 15204397).card = 1293 := by
  simpa using combineTwinPrimeSegments (by decide : 14942253 ≤ 15073325)
    (by decide : 15073325 ≤ 15204397) S007C02.total S007C03.total

theorem join_0_2 : (twinPrimeSegment 15204397 15466541).card = 1283 := by
  simpa using combineTwinPrimeSegments (by decide : 15204397 ≤ 15335469)
    (by decide : 15335469 ≤ 15466541) S007C04.total S007C05.total

theorem join_0_3 : (twinPrimeSegment 15466541 15728685).card = 1298 := by
  simpa using combineTwinPrimeSegments (by decide : 15466541 ≤ 15597613)
    (by decide : 15597613 ≤ 15728685) S007C06.total S007C07.total

theorem join_0_4 : (twinPrimeSegment 15728685 15990829).card = 1256 := by
  simpa using combineTwinPrimeSegments (by decide : 15728685 ≤ 15859757)
    (by decide : 15859757 ≤ 15990829) S007C08.total S007C09.total

theorem join_0_5 : (twinPrimeSegment 15990829 16252973).card = 1219 := by
  simpa using combineTwinPrimeSegments (by decide : 15990829 ≤ 16121901)
    (by decide : 16121901 ≤ 16252973) S007C10.total S007C11.total

theorem join_0_6 : (twinPrimeSegment 16252973 16515117).card = 1259 := by
  simpa using combineTwinPrimeSegments (by decide : 16252973 ≤ 16384045)
    (by decide : 16384045 ≤ 16515117) S007C12.total S007C13.total

theorem join_0_7 : (twinPrimeSegment 16515117 16777261).card = 1279 := by
  simpa using combineTwinPrimeSegments (by decide : 16515117 ≤ 16646189)
    (by decide : 16646189 ≤ 16777261) S007C14.total S007C15.total

theorem join_1_0 : (twinPrimeSegment 14680109 15204397).card = 2549 := by
  simpa using combineTwinPrimeSegments (by decide : 14680109 ≤ 14942253)
    (by decide : 14942253 ≤ 15204397) join_0_0 join_0_1

theorem join_1_1 : (twinPrimeSegment 15204397 15728685).card = 2581 := by
  simpa using combineTwinPrimeSegments (by decide : 15204397 ≤ 15466541)
    (by decide : 15466541 ≤ 15728685) join_0_2 join_0_3

theorem join_1_2 : (twinPrimeSegment 15728685 16252973).card = 2475 := by
  simpa using combineTwinPrimeSegments (by decide : 15728685 ≤ 15990829)
    (by decide : 15990829 ≤ 16252973) join_0_4 join_0_5

theorem join_1_3 : (twinPrimeSegment 16252973 16777261).card = 2538 := by
  simpa using combineTwinPrimeSegments (by decide : 16252973 ≤ 16515117)
    (by decide : 16515117 ≤ 16777261) join_0_6 join_0_7

theorem join_2_0 : (twinPrimeSegment 14680109 15728685).card = 5130 := by
  simpa using combineTwinPrimeSegments (by decide : 14680109 ≤ 15204397)
    (by decide : 15204397 ≤ 15728685) join_1_0 join_1_1

theorem join_2_1 : (twinPrimeSegment 15728685 16777261).card = 5013 := by
  simpa using combineTwinPrimeSegments (by decide : 15728685 ≤ 16252973)
    (by decide : 16252973 ≤ 16777261) join_1_2 join_1_3

theorem join_3_0 : (twinPrimeSegment 14680109 16777261).card = 10143 := by
  simpa using combineTwinPrimeSegments (by decide : 14680109 ≤ 15728685)
    (by decide : 15728685 ≤ 16777261) join_2_0 join_2_1

theorem total : (twinPrimeSegment 14680109 16777261).card = 10143 := join_3_0

end S007All
end Sude.GeneratedTwinScan
