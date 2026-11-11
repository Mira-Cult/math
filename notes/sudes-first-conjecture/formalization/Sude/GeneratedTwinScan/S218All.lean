import Sude.GeneratedTwinScan.S218C00
import Sude.GeneratedTwinScan.S218C01
import Sude.GeneratedTwinScan.S218C02
import Sude.GeneratedTwinScan.S218C03
import Sude.GeneratedTwinScan.S218C04
import Sude.GeneratedTwinScan.S218C05
import Sude.GeneratedTwinScan.S218C06
import Sude.GeneratedTwinScan.S218C07
import Sude.GeneratedTwinScan.S218C08
import Sude.GeneratedTwinScan.S218C09
import Sude.GeneratedTwinScan.S218C10
import Sude.GeneratedTwinScan.S218C11
import Sude.GeneratedTwinScan.S218C12
import Sude.GeneratedTwinScan.S218C13
import Sude.GeneratedTwinScan.S218C14
import Sude.GeneratedTwinScan.S218C15

/-! Combined FT source segment; Lean kernel check required. -/
namespace Sude.GeneratedTwinScan
namespace S218All

theorem join_0_0 : (twinPrimeSegment 457179181 457441325).card = 879 := by
  simpa using combineTwinPrimeSegments (by decide : 457179181 ≤ 457310253)
    (by decide : 457310253 ≤ 457441325) S218C00.total S218C01.total

theorem join_0_1 : (twinPrimeSegment 457441325 457703469).card = 878 := by
  simpa using combineTwinPrimeSegments (by decide : 457441325 ≤ 457572397)
    (by decide : 457572397 ≤ 457703469) S218C02.total S218C03.total

theorem join_0_2 : (twinPrimeSegment 457703469 457965613).card = 826 := by
  simpa using combineTwinPrimeSegments (by decide : 457703469 ≤ 457834541)
    (by decide : 457834541 ≤ 457965613) S218C04.total S218C05.total

theorem join_0_3 : (twinPrimeSegment 457965613 458227757).card = 893 := by
  simpa using combineTwinPrimeSegments (by decide : 457965613 ≤ 458096685)
    (by decide : 458096685 ≤ 458227757) S218C06.total S218C07.total

theorem join_0_4 : (twinPrimeSegment 458227757 458489901).card = 865 := by
  simpa using combineTwinPrimeSegments (by decide : 458227757 ≤ 458358829)
    (by decide : 458358829 ≤ 458489901) S218C08.total S218C09.total

theorem join_0_5 : (twinPrimeSegment 458489901 458752045).card = 879 := by
  simpa using combineTwinPrimeSegments (by decide : 458489901 ≤ 458620973)
    (by decide : 458620973 ≤ 458752045) S218C10.total S218C11.total

theorem join_0_6 : (twinPrimeSegment 458752045 459014189).card = 824 := by
  simpa using combineTwinPrimeSegments (by decide : 458752045 ≤ 458883117)
    (by decide : 458883117 ≤ 459014189) S218C12.total S218C13.total

theorem join_0_7 : (twinPrimeSegment 459014189 459276333).card = 905 := by
  simpa using combineTwinPrimeSegments (by decide : 459014189 ≤ 459145261)
    (by decide : 459145261 ≤ 459276333) S218C14.total S218C15.total

theorem join_1_0 : (twinPrimeSegment 457179181 457703469).card = 1757 := by
  simpa using combineTwinPrimeSegments (by decide : 457179181 ≤ 457441325)
    (by decide : 457441325 ≤ 457703469) join_0_0 join_0_1

theorem join_1_1 : (twinPrimeSegment 457703469 458227757).card = 1719 := by
  simpa using combineTwinPrimeSegments (by decide : 457703469 ≤ 457965613)
    (by decide : 457965613 ≤ 458227757) join_0_2 join_0_3

theorem join_1_2 : (twinPrimeSegment 458227757 458752045).card = 1744 := by
  simpa using combineTwinPrimeSegments (by decide : 458227757 ≤ 458489901)
    (by decide : 458489901 ≤ 458752045) join_0_4 join_0_5

theorem join_1_3 : (twinPrimeSegment 458752045 459276333).card = 1729 := by
  simpa using combineTwinPrimeSegments (by decide : 458752045 ≤ 459014189)
    (by decide : 459014189 ≤ 459276333) join_0_6 join_0_7

theorem join_2_0 : (twinPrimeSegment 457179181 458227757).card = 3476 := by
  simpa using combineTwinPrimeSegments (by decide : 457179181 ≤ 457703469)
    (by decide : 457703469 ≤ 458227757) join_1_0 join_1_1

theorem join_2_1 : (twinPrimeSegment 458227757 459276333).card = 3473 := by
  simpa using combineTwinPrimeSegments (by decide : 458227757 ≤ 458752045)
    (by decide : 458752045 ≤ 459276333) join_1_2 join_1_3

theorem join_3_0 : (twinPrimeSegment 457179181 459276333).card = 6949 := by
  simpa using combineTwinPrimeSegments (by decide : 457179181 ≤ 458227757)
    (by decide : 458227757 ≤ 459276333) join_2_0 join_2_1

theorem total : (twinPrimeSegment 457179181 459276333).card = 6949 := join_3_0

end S218All
end Sude.GeneratedTwinScan
