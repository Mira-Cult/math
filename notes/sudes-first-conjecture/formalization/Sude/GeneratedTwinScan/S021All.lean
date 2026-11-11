import Sude.GeneratedTwinScan.S021C00
import Sude.GeneratedTwinScan.S021C01
import Sude.GeneratedTwinScan.S021C02
import Sude.GeneratedTwinScan.S021C03
import Sude.GeneratedTwinScan.S021C04
import Sude.GeneratedTwinScan.S021C05
import Sude.GeneratedTwinScan.S021C06
import Sude.GeneratedTwinScan.S021C07
import Sude.GeneratedTwinScan.S021C08
import Sude.GeneratedTwinScan.S021C09
import Sude.GeneratedTwinScan.S021C10
import Sude.GeneratedTwinScan.S021C11
import Sude.GeneratedTwinScan.S021C12
import Sude.GeneratedTwinScan.S021C13
import Sude.GeneratedTwinScan.S021C14
import Sude.GeneratedTwinScan.S021C15

/-! Combined FT source segment; Lean kernel check required. -/
namespace Sude.GeneratedTwinScan
namespace S021All

theorem join_0_0 : (twinPrimeSegment 44040237 44302381).card = 1141 := by
  simpa using combineTwinPrimeSegments (by decide : 44040237 ≤ 44171309)
    (by decide : 44171309 ≤ 44302381) S021C00.total S021C01.total

theorem join_0_1 : (twinPrimeSegment 44302381 44564525).card = 1088 := by
  simpa using combineTwinPrimeSegments (by decide : 44302381 ≤ 44433453)
    (by decide : 44433453 ≤ 44564525) S021C02.total S021C03.total

theorem join_0_2 : (twinPrimeSegment 44564525 44826669).card = 1133 := by
  simpa using combineTwinPrimeSegments (by decide : 44564525 ≤ 44695597)
    (by decide : 44695597 ≤ 44826669) S021C04.total S021C05.total

theorem join_0_3 : (twinPrimeSegment 44826669 45088813).card = 1097 := by
  simpa using combineTwinPrimeSegments (by decide : 44826669 ≤ 44957741)
    (by decide : 44957741 ≤ 45088813) S021C06.total S021C07.total

theorem join_0_4 : (twinPrimeSegment 45088813 45350957).card = 1095 := by
  simpa using combineTwinPrimeSegments (by decide : 45088813 ≤ 45219885)
    (by decide : 45219885 ≤ 45350957) S021C08.total S021C09.total

theorem join_0_5 : (twinPrimeSegment 45350957 45613101).card = 1127 := by
  simpa using combineTwinPrimeSegments (by decide : 45350957 ≤ 45482029)
    (by decide : 45482029 ≤ 45613101) S021C10.total S021C11.total

theorem join_0_6 : (twinPrimeSegment 45613101 45875245).card = 1133 := by
  simpa using combineTwinPrimeSegments (by decide : 45613101 ≤ 45744173)
    (by decide : 45744173 ≤ 45875245) S021C12.total S021C13.total

theorem join_0_7 : (twinPrimeSegment 45875245 46137389).card = 1098 := by
  simpa using combineTwinPrimeSegments (by decide : 45875245 ≤ 46006317)
    (by decide : 46006317 ≤ 46137389) S021C14.total S021C15.total

theorem join_1_0 : (twinPrimeSegment 44040237 44564525).card = 2229 := by
  simpa using combineTwinPrimeSegments (by decide : 44040237 ≤ 44302381)
    (by decide : 44302381 ≤ 44564525) join_0_0 join_0_1

theorem join_1_1 : (twinPrimeSegment 44564525 45088813).card = 2230 := by
  simpa using combineTwinPrimeSegments (by decide : 44564525 ≤ 44826669)
    (by decide : 44826669 ≤ 45088813) join_0_2 join_0_3

theorem join_1_2 : (twinPrimeSegment 45088813 45613101).card = 2222 := by
  simpa using combineTwinPrimeSegments (by decide : 45088813 ≤ 45350957)
    (by decide : 45350957 ≤ 45613101) join_0_4 join_0_5

theorem join_1_3 : (twinPrimeSegment 45613101 46137389).card = 2231 := by
  simpa using combineTwinPrimeSegments (by decide : 45613101 ≤ 45875245)
    (by decide : 45875245 ≤ 46137389) join_0_6 join_0_7

theorem join_2_0 : (twinPrimeSegment 44040237 45088813).card = 4459 := by
  simpa using combineTwinPrimeSegments (by decide : 44040237 ≤ 44564525)
    (by decide : 44564525 ≤ 45088813) join_1_0 join_1_1

theorem join_2_1 : (twinPrimeSegment 45088813 46137389).card = 4453 := by
  simpa using combineTwinPrimeSegments (by decide : 45088813 ≤ 45613101)
    (by decide : 45613101 ≤ 46137389) join_1_2 join_1_3

theorem join_3_0 : (twinPrimeSegment 44040237 46137389).card = 8912 := by
  simpa using combineTwinPrimeSegments (by decide : 44040237 ≤ 45088813)
    (by decide : 45088813 ≤ 46137389) join_2_0 join_2_1

theorem total : (twinPrimeSegment 44040237 46137389).card = 8912 := join_3_0

end S021All
end Sude.GeneratedTwinScan
