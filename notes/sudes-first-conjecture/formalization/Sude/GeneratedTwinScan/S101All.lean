import Sude.GeneratedTwinScan.S101C00
import Sude.GeneratedTwinScan.S101C01
import Sude.GeneratedTwinScan.S101C02
import Sude.GeneratedTwinScan.S101C03
import Sude.GeneratedTwinScan.S101C04
import Sude.GeneratedTwinScan.S101C05
import Sude.GeneratedTwinScan.S101C06
import Sude.GeneratedTwinScan.S101C07
import Sude.GeneratedTwinScan.S101C08
import Sude.GeneratedTwinScan.S101C09
import Sude.GeneratedTwinScan.S101C10
import Sude.GeneratedTwinScan.S101C11
import Sude.GeneratedTwinScan.S101C12
import Sude.GeneratedTwinScan.S101C13
import Sude.GeneratedTwinScan.S101C14
import Sude.GeneratedTwinScan.S101C15

/-! Combined FT source segment; Lean kernel check required. -/
namespace Sude.GeneratedTwinScan
namespace S101All

theorem join_0_0 : (twinPrimeSegment 211812397 212074541).card = 995 := by
  simpa using combineTwinPrimeSegments (by decide : 211812397 ≤ 211943469)
    (by decide : 211943469 ≤ 212074541) S101C00.total S101C01.total

theorem join_0_1 : (twinPrimeSegment 212074541 212336685).card = 908 := by
  simpa using combineTwinPrimeSegments (by decide : 212074541 ≤ 212205613)
    (by decide : 212205613 ≤ 212336685) S101C02.total S101C03.total

theorem join_0_2 : (twinPrimeSegment 212336685 212598829).card = 912 := by
  simpa using combineTwinPrimeSegments (by decide : 212336685 ≤ 212467757)
    (by decide : 212467757 ≤ 212598829) S101C04.total S101C05.total

theorem join_0_3 : (twinPrimeSegment 212598829 212860973).card = 946 := by
  simpa using combineTwinPrimeSegments (by decide : 212598829 ≤ 212729901)
    (by decide : 212729901 ≤ 212860973) S101C06.total S101C07.total

theorem join_0_4 : (twinPrimeSegment 212860973 213123117).card = 968 := by
  simpa using combineTwinPrimeSegments (by decide : 212860973 ≤ 212992045)
    (by decide : 212992045 ≤ 213123117) S101C08.total S101C09.total

theorem join_0_5 : (twinPrimeSegment 213123117 213385261).card = 941 := by
  simpa using combineTwinPrimeSegments (by decide : 213123117 ≤ 213254189)
    (by decide : 213254189 ≤ 213385261) S101C10.total S101C11.total

theorem join_0_6 : (twinPrimeSegment 213385261 213647405).card = 948 := by
  simpa using combineTwinPrimeSegments (by decide : 213385261 ≤ 213516333)
    (by decide : 213516333 ≤ 213647405) S101C12.total S101C13.total

theorem join_0_7 : (twinPrimeSegment 213647405 213909549).card = 902 := by
  simpa using combineTwinPrimeSegments (by decide : 213647405 ≤ 213778477)
    (by decide : 213778477 ≤ 213909549) S101C14.total S101C15.total

theorem join_1_0 : (twinPrimeSegment 211812397 212336685).card = 1903 := by
  simpa using combineTwinPrimeSegments (by decide : 211812397 ≤ 212074541)
    (by decide : 212074541 ≤ 212336685) join_0_0 join_0_1

theorem join_1_1 : (twinPrimeSegment 212336685 212860973).card = 1858 := by
  simpa using combineTwinPrimeSegments (by decide : 212336685 ≤ 212598829)
    (by decide : 212598829 ≤ 212860973) join_0_2 join_0_3

theorem join_1_2 : (twinPrimeSegment 212860973 213385261).card = 1909 := by
  simpa using combineTwinPrimeSegments (by decide : 212860973 ≤ 213123117)
    (by decide : 213123117 ≤ 213385261) join_0_4 join_0_5

theorem join_1_3 : (twinPrimeSegment 213385261 213909549).card = 1850 := by
  simpa using combineTwinPrimeSegments (by decide : 213385261 ≤ 213647405)
    (by decide : 213647405 ≤ 213909549) join_0_6 join_0_7

theorem join_2_0 : (twinPrimeSegment 211812397 212860973).card = 3761 := by
  simpa using combineTwinPrimeSegments (by decide : 211812397 ≤ 212336685)
    (by decide : 212336685 ≤ 212860973) join_1_0 join_1_1

theorem join_2_1 : (twinPrimeSegment 212860973 213909549).card = 3759 := by
  simpa using combineTwinPrimeSegments (by decide : 212860973 ≤ 213385261)
    (by decide : 213385261 ≤ 213909549) join_1_2 join_1_3

theorem join_3_0 : (twinPrimeSegment 211812397 213909549).card = 7520 := by
  simpa using combineTwinPrimeSegments (by decide : 211812397 ≤ 212860973)
    (by decide : 212860973 ≤ 213909549) join_2_0 join_2_1

theorem total : (twinPrimeSegment 211812397 213909549).card = 7520 := join_3_0

end S101All
end Sude.GeneratedTwinScan
