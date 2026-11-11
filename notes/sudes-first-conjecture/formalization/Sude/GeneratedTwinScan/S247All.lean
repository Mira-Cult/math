import Sude.GeneratedTwinScan.S247C00
import Sude.GeneratedTwinScan.S247C01
import Sude.GeneratedTwinScan.S247C02
import Sude.GeneratedTwinScan.S247C03
import Sude.GeneratedTwinScan.S247C04
import Sude.GeneratedTwinScan.S247C05
import Sude.GeneratedTwinScan.S247C06
import Sude.GeneratedTwinScan.S247C07
import Sude.GeneratedTwinScan.S247C08
import Sude.GeneratedTwinScan.S247C09
import Sude.GeneratedTwinScan.S247C10
import Sude.GeneratedTwinScan.S247C11
import Sude.GeneratedTwinScan.S247C12
import Sude.GeneratedTwinScan.S247C13
import Sude.GeneratedTwinScan.S247C14
import Sude.GeneratedTwinScan.S247C15

/-! Combined FT source segment; Lean kernel check required. -/
namespace Sude.GeneratedTwinScan
namespace S247All

theorem join_0_0 : (twinPrimeSegment 517996589 518258733).card = 857 := by
  simpa using combineTwinPrimeSegments (by decide : 517996589 ≤ 518127661)
    (by decide : 518127661 ≤ 518258733) S247C00.total S247C01.total

theorem join_0_1 : (twinPrimeSegment 518258733 518520877).card = 917 := by
  simpa using combineTwinPrimeSegments (by decide : 518258733 ≤ 518389805)
    (by decide : 518389805 ≤ 518520877) S247C02.total S247C03.total

theorem join_0_2 : (twinPrimeSegment 518520877 518783021).card = 858 := by
  simpa using combineTwinPrimeSegments (by decide : 518520877 ≤ 518651949)
    (by decide : 518651949 ≤ 518783021) S247C04.total S247C05.total

theorem join_0_3 : (twinPrimeSegment 518783021 519045165).card = 862 := by
  simpa using combineTwinPrimeSegments (by decide : 518783021 ≤ 518914093)
    (by decide : 518914093 ≤ 519045165) S247C06.total S247C07.total

theorem join_0_4 : (twinPrimeSegment 519045165 519307309).card = 812 := by
  simpa using combineTwinPrimeSegments (by decide : 519045165 ≤ 519176237)
    (by decide : 519176237 ≤ 519307309) S247C08.total S247C09.total

theorem join_0_5 : (twinPrimeSegment 519307309 519569453).card = 855 := by
  simpa using combineTwinPrimeSegments (by decide : 519307309 ≤ 519438381)
    (by decide : 519438381 ≤ 519569453) S247C10.total S247C11.total

theorem join_0_6 : (twinPrimeSegment 519569453 519831597).card = 925 := by
  simpa using combineTwinPrimeSegments (by decide : 519569453 ≤ 519700525)
    (by decide : 519700525 ≤ 519831597) S247C12.total S247C13.total

theorem join_0_7 : (twinPrimeSegment 519831597 520093741).card = 854 := by
  simpa using combineTwinPrimeSegments (by decide : 519831597 ≤ 519962669)
    (by decide : 519962669 ≤ 520093741) S247C14.total S247C15.total

theorem join_1_0 : (twinPrimeSegment 517996589 518520877).card = 1774 := by
  simpa using combineTwinPrimeSegments (by decide : 517996589 ≤ 518258733)
    (by decide : 518258733 ≤ 518520877) join_0_0 join_0_1

theorem join_1_1 : (twinPrimeSegment 518520877 519045165).card = 1720 := by
  simpa using combineTwinPrimeSegments (by decide : 518520877 ≤ 518783021)
    (by decide : 518783021 ≤ 519045165) join_0_2 join_0_3

theorem join_1_2 : (twinPrimeSegment 519045165 519569453).card = 1667 := by
  simpa using combineTwinPrimeSegments (by decide : 519045165 ≤ 519307309)
    (by decide : 519307309 ≤ 519569453) join_0_4 join_0_5

theorem join_1_3 : (twinPrimeSegment 519569453 520093741).card = 1779 := by
  simpa using combineTwinPrimeSegments (by decide : 519569453 ≤ 519831597)
    (by decide : 519831597 ≤ 520093741) join_0_6 join_0_7

theorem join_2_0 : (twinPrimeSegment 517996589 519045165).card = 3494 := by
  simpa using combineTwinPrimeSegments (by decide : 517996589 ≤ 518520877)
    (by decide : 518520877 ≤ 519045165) join_1_0 join_1_1

theorem join_2_1 : (twinPrimeSegment 519045165 520093741).card = 3446 := by
  simpa using combineTwinPrimeSegments (by decide : 519045165 ≤ 519569453)
    (by decide : 519569453 ≤ 520093741) join_1_2 join_1_3

theorem join_3_0 : (twinPrimeSegment 517996589 520093741).card = 6940 := by
  simpa using combineTwinPrimeSegments (by decide : 517996589 ≤ 519045165)
    (by decide : 519045165 ≤ 520093741) join_2_0 join_2_1

theorem total : (twinPrimeSegment 517996589 520093741).card = 6940 := join_3_0

end S247All
end Sude.GeneratedTwinScan
