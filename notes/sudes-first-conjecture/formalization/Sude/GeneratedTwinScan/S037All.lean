import Sude.GeneratedTwinScan.S037C00
import Sude.GeneratedTwinScan.S037C01
import Sude.GeneratedTwinScan.S037C02
import Sude.GeneratedTwinScan.S037C03
import Sude.GeneratedTwinScan.S037C04
import Sude.GeneratedTwinScan.S037C05
import Sude.GeneratedTwinScan.S037C06
import Sude.GeneratedTwinScan.S037C07
import Sude.GeneratedTwinScan.S037C08
import Sude.GeneratedTwinScan.S037C09
import Sude.GeneratedTwinScan.S037C10
import Sude.GeneratedTwinScan.S037C11
import Sude.GeneratedTwinScan.S037C12
import Sude.GeneratedTwinScan.S037C13
import Sude.GeneratedTwinScan.S037C14
import Sude.GeneratedTwinScan.S037C15

/-! Combined FT source segment; Lean kernel check required. -/
namespace Sude.GeneratedTwinScan
namespace S037All

theorem join_0_0 : (twinPrimeSegment 77594669 77856813).card = 1053 := by
  simpa using combineTwinPrimeSegments (by decide : 77594669 ≤ 77725741)
    (by decide : 77725741 ≤ 77856813) S037C00.total S037C01.total

theorem join_0_1 : (twinPrimeSegment 77856813 78118957).card = 1055 := by
  simpa using combineTwinPrimeSegments (by decide : 77856813 ≤ 77987885)
    (by decide : 77987885 ≤ 78118957) S037C02.total S037C03.total

theorem join_0_2 : (twinPrimeSegment 78118957 78381101).card = 1038 := by
  simpa using combineTwinPrimeSegments (by decide : 78118957 ≤ 78250029)
    (by decide : 78250029 ≤ 78381101) S037C04.total S037C05.total

theorem join_0_3 : (twinPrimeSegment 78381101 78643245).card = 1042 := by
  simpa using combineTwinPrimeSegments (by decide : 78381101 ≤ 78512173)
    (by decide : 78512173 ≤ 78643245) S037C06.total S037C07.total

theorem join_0_4 : (twinPrimeSegment 78643245 78905389).card = 1037 := by
  simpa using combineTwinPrimeSegments (by decide : 78643245 ≤ 78774317)
    (by decide : 78774317 ≤ 78905389) S037C08.total S037C09.total

theorem join_0_5 : (twinPrimeSegment 78905389 79167533).card = 1026 := by
  simpa using combineTwinPrimeSegments (by decide : 78905389 ≤ 79036461)
    (by decide : 79036461 ≤ 79167533) S037C10.total S037C11.total

theorem join_0_6 : (twinPrimeSegment 79167533 79429677).card = 1028 := by
  simpa using combineTwinPrimeSegments (by decide : 79167533 ≤ 79298605)
    (by decide : 79298605 ≤ 79429677) S037C12.total S037C13.total

theorem join_0_7 : (twinPrimeSegment 79429677 79691821).card = 1037 := by
  simpa using combineTwinPrimeSegments (by decide : 79429677 ≤ 79560749)
    (by decide : 79560749 ≤ 79691821) S037C14.total S037C15.total

theorem join_1_0 : (twinPrimeSegment 77594669 78118957).card = 2108 := by
  simpa using combineTwinPrimeSegments (by decide : 77594669 ≤ 77856813)
    (by decide : 77856813 ≤ 78118957) join_0_0 join_0_1

theorem join_1_1 : (twinPrimeSegment 78118957 78643245).card = 2080 := by
  simpa using combineTwinPrimeSegments (by decide : 78118957 ≤ 78381101)
    (by decide : 78381101 ≤ 78643245) join_0_2 join_0_3

theorem join_1_2 : (twinPrimeSegment 78643245 79167533).card = 2063 := by
  simpa using combineTwinPrimeSegments (by decide : 78643245 ≤ 78905389)
    (by decide : 78905389 ≤ 79167533) join_0_4 join_0_5

theorem join_1_3 : (twinPrimeSegment 79167533 79691821).card = 2065 := by
  simpa using combineTwinPrimeSegments (by decide : 79167533 ≤ 79429677)
    (by decide : 79429677 ≤ 79691821) join_0_6 join_0_7

theorem join_2_0 : (twinPrimeSegment 77594669 78643245).card = 4188 := by
  simpa using combineTwinPrimeSegments (by decide : 77594669 ≤ 78118957)
    (by decide : 78118957 ≤ 78643245) join_1_0 join_1_1

theorem join_2_1 : (twinPrimeSegment 78643245 79691821).card = 4128 := by
  simpa using combineTwinPrimeSegments (by decide : 78643245 ≤ 79167533)
    (by decide : 79167533 ≤ 79691821) join_1_2 join_1_3

theorem join_3_0 : (twinPrimeSegment 77594669 79691821).card = 8316 := by
  simpa using combineTwinPrimeSegments (by decide : 77594669 ≤ 78643245)
    (by decide : 78643245 ≤ 79691821) join_2_0 join_2_1

theorem total : (twinPrimeSegment 77594669 79691821).card = 8316 := join_3_0

end S037All
end Sude.GeneratedTwinScan
