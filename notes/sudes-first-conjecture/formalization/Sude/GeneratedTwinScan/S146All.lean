import Sude.GeneratedTwinScan.S146C00
import Sude.GeneratedTwinScan.S146C01
import Sude.GeneratedTwinScan.S146C02
import Sude.GeneratedTwinScan.S146C03
import Sude.GeneratedTwinScan.S146C04
import Sude.GeneratedTwinScan.S146C05
import Sude.GeneratedTwinScan.S146C06
import Sude.GeneratedTwinScan.S146C07
import Sude.GeneratedTwinScan.S146C08
import Sude.GeneratedTwinScan.S146C09
import Sude.GeneratedTwinScan.S146C10
import Sude.GeneratedTwinScan.S146C11
import Sude.GeneratedTwinScan.S146C12
import Sude.GeneratedTwinScan.S146C13
import Sude.GeneratedTwinScan.S146C14
import Sude.GeneratedTwinScan.S146C15

/-! Combined FT source segment; Lean kernel check required. -/
namespace Sude.GeneratedTwinScan
namespace S146All

theorem join_0_0 : (twinPrimeSegment 306184237 306446381).card = 883 := by
  simpa using combineTwinPrimeSegments (by decide : 306184237 ≤ 306315309)
    (by decide : 306315309 ≤ 306446381) S146C00.total S146C01.total

theorem join_0_1 : (twinPrimeSegment 306446381 306708525).card = 915 := by
  simpa using combineTwinPrimeSegments (by decide : 306446381 ≤ 306577453)
    (by decide : 306577453 ≤ 306708525) S146C02.total S146C03.total

theorem join_0_2 : (twinPrimeSegment 306708525 306970669).card = 945 := by
  simpa using combineTwinPrimeSegments (by decide : 306708525 ≤ 306839597)
    (by decide : 306839597 ≤ 306970669) S146C04.total S146C05.total

theorem join_0_3 : (twinPrimeSegment 306970669 307232813).card = 935 := by
  simpa using combineTwinPrimeSegments (by decide : 306970669 ≤ 307101741)
    (by decide : 307101741 ≤ 307232813) S146C06.total S146C07.total

theorem join_0_4 : (twinPrimeSegment 307232813 307494957).card = 903 := by
  simpa using combineTwinPrimeSegments (by decide : 307232813 ≤ 307363885)
    (by decide : 307363885 ≤ 307494957) S146C08.total S146C09.total

theorem join_0_5 : (twinPrimeSegment 307494957 307757101).card = 889 := by
  simpa using combineTwinPrimeSegments (by decide : 307494957 ≤ 307626029)
    (by decide : 307626029 ≤ 307757101) S146C10.total S146C11.total

theorem join_0_6 : (twinPrimeSegment 307757101 308019245).card = 963 := by
  simpa using combineTwinPrimeSegments (by decide : 307757101 ≤ 307888173)
    (by decide : 307888173 ≤ 308019245) S146C12.total S146C13.total

theorem join_0_7 : (twinPrimeSegment 308019245 308281389).card = 909 := by
  simpa using combineTwinPrimeSegments (by decide : 308019245 ≤ 308150317)
    (by decide : 308150317 ≤ 308281389) S146C14.total S146C15.total

theorem join_1_0 : (twinPrimeSegment 306184237 306708525).card = 1798 := by
  simpa using combineTwinPrimeSegments (by decide : 306184237 ≤ 306446381)
    (by decide : 306446381 ≤ 306708525) join_0_0 join_0_1

theorem join_1_1 : (twinPrimeSegment 306708525 307232813).card = 1880 := by
  simpa using combineTwinPrimeSegments (by decide : 306708525 ≤ 306970669)
    (by decide : 306970669 ≤ 307232813) join_0_2 join_0_3

theorem join_1_2 : (twinPrimeSegment 307232813 307757101).card = 1792 := by
  simpa using combineTwinPrimeSegments (by decide : 307232813 ≤ 307494957)
    (by decide : 307494957 ≤ 307757101) join_0_4 join_0_5

theorem join_1_3 : (twinPrimeSegment 307757101 308281389).card = 1872 := by
  simpa using combineTwinPrimeSegments (by decide : 307757101 ≤ 308019245)
    (by decide : 308019245 ≤ 308281389) join_0_6 join_0_7

theorem join_2_0 : (twinPrimeSegment 306184237 307232813).card = 3678 := by
  simpa using combineTwinPrimeSegments (by decide : 306184237 ≤ 306708525)
    (by decide : 306708525 ≤ 307232813) join_1_0 join_1_1

theorem join_2_1 : (twinPrimeSegment 307232813 308281389).card = 3664 := by
  simpa using combineTwinPrimeSegments (by decide : 307232813 ≤ 307757101)
    (by decide : 307757101 ≤ 308281389) join_1_2 join_1_3

theorem join_3_0 : (twinPrimeSegment 306184237 308281389).card = 7342 := by
  simpa using combineTwinPrimeSegments (by decide : 306184237 ≤ 307232813)
    (by decide : 307232813 ≤ 308281389) join_2_0 join_2_1

theorem total : (twinPrimeSegment 306184237 308281389).card = 7342 := join_3_0

end S146All
end Sude.GeneratedTwinScan
