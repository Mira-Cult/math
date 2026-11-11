import Sude.GeneratedTwinScan.S068C00
import Sude.GeneratedTwinScan.S068C01
import Sude.GeneratedTwinScan.S068C02
import Sude.GeneratedTwinScan.S068C03
import Sude.GeneratedTwinScan.S068C04
import Sude.GeneratedTwinScan.S068C05
import Sude.GeneratedTwinScan.S068C06
import Sude.GeneratedTwinScan.S068C07
import Sude.GeneratedTwinScan.S068C08
import Sude.GeneratedTwinScan.S068C09
import Sude.GeneratedTwinScan.S068C10
import Sude.GeneratedTwinScan.S068C11
import Sude.GeneratedTwinScan.S068C12
import Sude.GeneratedTwinScan.S068C13
import Sude.GeneratedTwinScan.S068C14
import Sude.GeneratedTwinScan.S068C15

/-! Combined FT source segment; Lean kernel check required. -/
namespace Sude.GeneratedTwinScan
namespace S068All

theorem join_0_0 : (twinPrimeSegment 142606381 142868525).card = 968 := by
  simpa using combineTwinPrimeSegments (by decide : 142606381 ≤ 142737453)
    (by decide : 142737453 ≤ 142868525) S068C00.total S068C01.total

theorem join_0_1 : (twinPrimeSegment 142868525 143130669).card = 1003 := by
  simpa using combineTwinPrimeSegments (by decide : 142868525 ≤ 142999597)
    (by decide : 142999597 ≤ 143130669) S068C02.total S068C03.total

theorem join_0_2 : (twinPrimeSegment 143130669 143392813).card = 1004 := by
  simpa using combineTwinPrimeSegments (by decide : 143130669 ≤ 143261741)
    (by decide : 143261741 ≤ 143392813) S068C04.total S068C05.total

theorem join_0_3 : (twinPrimeSegment 143392813 143654957).card = 998 := by
  simpa using combineTwinPrimeSegments (by decide : 143392813 ≤ 143523885)
    (by decide : 143523885 ≤ 143654957) S068C06.total S068C07.total

theorem join_0_4 : (twinPrimeSegment 143654957 143917101).card = 987 := by
  simpa using combineTwinPrimeSegments (by decide : 143654957 ≤ 143786029)
    (by decide : 143786029 ≤ 143917101) S068C08.total S068C09.total

theorem join_0_5 : (twinPrimeSegment 143917101 144179245).card = 1017 := by
  simpa using combineTwinPrimeSegments (by decide : 143917101 ≤ 144048173)
    (by decide : 144048173 ≤ 144179245) S068C10.total S068C11.total

theorem join_0_6 : (twinPrimeSegment 144179245 144441389).card = 994 := by
  simpa using combineTwinPrimeSegments (by decide : 144179245 ≤ 144310317)
    (by decide : 144310317 ≤ 144441389) S068C12.total S068C13.total

theorem join_0_7 : (twinPrimeSegment 144441389 144703533).card = 963 := by
  simpa using combineTwinPrimeSegments (by decide : 144441389 ≤ 144572461)
    (by decide : 144572461 ≤ 144703533) S068C14.total S068C15.total

theorem join_1_0 : (twinPrimeSegment 142606381 143130669).card = 1971 := by
  simpa using combineTwinPrimeSegments (by decide : 142606381 ≤ 142868525)
    (by decide : 142868525 ≤ 143130669) join_0_0 join_0_1

theorem join_1_1 : (twinPrimeSegment 143130669 143654957).card = 2002 := by
  simpa using combineTwinPrimeSegments (by decide : 143130669 ≤ 143392813)
    (by decide : 143392813 ≤ 143654957) join_0_2 join_0_3

theorem join_1_2 : (twinPrimeSegment 143654957 144179245).card = 2004 := by
  simpa using combineTwinPrimeSegments (by decide : 143654957 ≤ 143917101)
    (by decide : 143917101 ≤ 144179245) join_0_4 join_0_5

theorem join_1_3 : (twinPrimeSegment 144179245 144703533).card = 1957 := by
  simpa using combineTwinPrimeSegments (by decide : 144179245 ≤ 144441389)
    (by decide : 144441389 ≤ 144703533) join_0_6 join_0_7

theorem join_2_0 : (twinPrimeSegment 142606381 143654957).card = 3973 := by
  simpa using combineTwinPrimeSegments (by decide : 142606381 ≤ 143130669)
    (by decide : 143130669 ≤ 143654957) join_1_0 join_1_1

theorem join_2_1 : (twinPrimeSegment 143654957 144703533).card = 3961 := by
  simpa using combineTwinPrimeSegments (by decide : 143654957 ≤ 144179245)
    (by decide : 144179245 ≤ 144703533) join_1_2 join_1_3

theorem join_3_0 : (twinPrimeSegment 142606381 144703533).card = 7934 := by
  simpa using combineTwinPrimeSegments (by decide : 142606381 ≤ 143654957)
    (by decide : 143654957 ≤ 144703533) join_2_0 join_2_1

theorem total : (twinPrimeSegment 142606381 144703533).card = 7934 := join_3_0

end S068All
end Sude.GeneratedTwinScan
