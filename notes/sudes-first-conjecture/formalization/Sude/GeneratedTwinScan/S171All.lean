import Sude.GeneratedTwinScan.S171C00
import Sude.GeneratedTwinScan.S171C01
import Sude.GeneratedTwinScan.S171C02
import Sude.GeneratedTwinScan.S171C03
import Sude.GeneratedTwinScan.S171C04
import Sude.GeneratedTwinScan.S171C05
import Sude.GeneratedTwinScan.S171C06
import Sude.GeneratedTwinScan.S171C07
import Sude.GeneratedTwinScan.S171C08
import Sude.GeneratedTwinScan.S171C09
import Sude.GeneratedTwinScan.S171C10
import Sude.GeneratedTwinScan.S171C11
import Sude.GeneratedTwinScan.S171C12
import Sude.GeneratedTwinScan.S171C13
import Sude.GeneratedTwinScan.S171C14
import Sude.GeneratedTwinScan.S171C15

/-! Combined FT source segment; Lean kernel check required. -/
namespace Sude.GeneratedTwinScan
namespace S171All

theorem join_0_0 : (twinPrimeSegment 358613037 358875181).card = 910 := by
  simpa using combineTwinPrimeSegments (by decide : 358613037 ≤ 358744109)
    (by decide : 358744109 ≤ 358875181) S171C00.total S171C01.total

theorem join_0_1 : (twinPrimeSegment 358875181 359137325).card = 897 := by
  simpa using combineTwinPrimeSegments (by decide : 358875181 ≤ 359006253)
    (by decide : 359006253 ≤ 359137325) S171C02.total S171C03.total

theorem join_0_2 : (twinPrimeSegment 359137325 359399469).card = 867 := by
  simpa using combineTwinPrimeSegments (by decide : 359137325 ≤ 359268397)
    (by decide : 359268397 ≤ 359399469) S171C04.total S171C05.total

theorem join_0_3 : (twinPrimeSegment 359399469 359661613).card = 874 := by
  simpa using combineTwinPrimeSegments (by decide : 359399469 ≤ 359530541)
    (by decide : 359530541 ≤ 359661613) S171C06.total S171C07.total

theorem join_0_4 : (twinPrimeSegment 359661613 359923757).card = 899 := by
  simpa using combineTwinPrimeSegments (by decide : 359661613 ≤ 359792685)
    (by decide : 359792685 ≤ 359923757) S171C08.total S171C09.total

theorem join_0_5 : (twinPrimeSegment 359923757 360185901).card = 817 := by
  simpa using combineTwinPrimeSegments (by decide : 359923757 ≤ 360054829)
    (by decide : 360054829 ≤ 360185901) S171C10.total S171C11.total

theorem join_0_6 : (twinPrimeSegment 360185901 360448045).card = 891 := by
  simpa using combineTwinPrimeSegments (by decide : 360185901 ≤ 360316973)
    (by decide : 360316973 ≤ 360448045) S171C12.total S171C13.total

theorem join_0_7 : (twinPrimeSegment 360448045 360710189).card = 905 := by
  simpa using combineTwinPrimeSegments (by decide : 360448045 ≤ 360579117)
    (by decide : 360579117 ≤ 360710189) S171C14.total S171C15.total

theorem join_1_0 : (twinPrimeSegment 358613037 359137325).card = 1807 := by
  simpa using combineTwinPrimeSegments (by decide : 358613037 ≤ 358875181)
    (by decide : 358875181 ≤ 359137325) join_0_0 join_0_1

theorem join_1_1 : (twinPrimeSegment 359137325 359661613).card = 1741 := by
  simpa using combineTwinPrimeSegments (by decide : 359137325 ≤ 359399469)
    (by decide : 359399469 ≤ 359661613) join_0_2 join_0_3

theorem join_1_2 : (twinPrimeSegment 359661613 360185901).card = 1716 := by
  simpa using combineTwinPrimeSegments (by decide : 359661613 ≤ 359923757)
    (by decide : 359923757 ≤ 360185901) join_0_4 join_0_5

theorem join_1_3 : (twinPrimeSegment 360185901 360710189).card = 1796 := by
  simpa using combineTwinPrimeSegments (by decide : 360185901 ≤ 360448045)
    (by decide : 360448045 ≤ 360710189) join_0_6 join_0_7

theorem join_2_0 : (twinPrimeSegment 358613037 359661613).card = 3548 := by
  simpa using combineTwinPrimeSegments (by decide : 358613037 ≤ 359137325)
    (by decide : 359137325 ≤ 359661613) join_1_0 join_1_1

theorem join_2_1 : (twinPrimeSegment 359661613 360710189).card = 3512 := by
  simpa using combineTwinPrimeSegments (by decide : 359661613 ≤ 360185901)
    (by decide : 360185901 ≤ 360710189) join_1_2 join_1_3

theorem join_3_0 : (twinPrimeSegment 358613037 360710189).card = 7060 := by
  simpa using combineTwinPrimeSegments (by decide : 358613037 ≤ 359661613)
    (by decide : 359661613 ≤ 360710189) join_2_0 join_2_1

theorem total : (twinPrimeSegment 358613037 360710189).card = 7060 := join_3_0

end S171All
end Sude.GeneratedTwinScan
