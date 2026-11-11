import Sude.GeneratedTwinScan.S224C00
import Sude.GeneratedTwinScan.S224C01
import Sude.GeneratedTwinScan.S224C02
import Sude.GeneratedTwinScan.S224C03
import Sude.GeneratedTwinScan.S224C04
import Sude.GeneratedTwinScan.S224C05
import Sude.GeneratedTwinScan.S224C06
import Sude.GeneratedTwinScan.S224C07
import Sude.GeneratedTwinScan.S224C08
import Sude.GeneratedTwinScan.S224C09
import Sude.GeneratedTwinScan.S224C10
import Sude.GeneratedTwinScan.S224C11
import Sude.GeneratedTwinScan.S224C12
import Sude.GeneratedTwinScan.S224C13
import Sude.GeneratedTwinScan.S224C14
import Sude.GeneratedTwinScan.S224C15

/-! Combined FT source segment; Lean kernel check required. -/
namespace Sude.GeneratedTwinScan
namespace S224All

theorem join_0_0 : (twinPrimeSegment 469762093 470024237).card = 892 := by
  simpa using combineTwinPrimeSegments (by decide : 469762093 ≤ 469893165)
    (by decide : 469893165 ≤ 470024237) S224C00.total S224C01.total

theorem join_0_1 : (twinPrimeSegment 470024237 470286381).card = 876 := by
  simpa using combineTwinPrimeSegments (by decide : 470024237 ≤ 470155309)
    (by decide : 470155309 ≤ 470286381) S224C02.total S224C03.total

theorem join_0_2 : (twinPrimeSegment 470286381 470548525).card = 877 := by
  simpa using combineTwinPrimeSegments (by decide : 470286381 ≤ 470417453)
    (by decide : 470417453 ≤ 470548525) S224C04.total S224C05.total

theorem join_0_3 : (twinPrimeSegment 470548525 470810669).card = 832 := by
  simpa using combineTwinPrimeSegments (by decide : 470548525 ≤ 470679597)
    (by decide : 470679597 ≤ 470810669) S224C06.total S224C07.total

theorem join_0_4 : (twinPrimeSegment 470810669 471072813).card = 860 := by
  simpa using combineTwinPrimeSegments (by decide : 470810669 ≤ 470941741)
    (by decide : 470941741 ≤ 471072813) S224C08.total S224C09.total

theorem join_0_5 : (twinPrimeSegment 471072813 471334957).card = 875 := by
  simpa using combineTwinPrimeSegments (by decide : 471072813 ≤ 471203885)
    (by decide : 471203885 ≤ 471334957) S224C10.total S224C11.total

theorem join_0_6 : (twinPrimeSegment 471334957 471597101).card = 893 := by
  simpa using combineTwinPrimeSegments (by decide : 471334957 ≤ 471466029)
    (by decide : 471466029 ≤ 471597101) S224C12.total S224C13.total

theorem join_0_7 : (twinPrimeSegment 471597101 471859245).card = 901 := by
  simpa using combineTwinPrimeSegments (by decide : 471597101 ≤ 471728173)
    (by decide : 471728173 ≤ 471859245) S224C14.total S224C15.total

theorem join_1_0 : (twinPrimeSegment 469762093 470286381).card = 1768 := by
  simpa using combineTwinPrimeSegments (by decide : 469762093 ≤ 470024237)
    (by decide : 470024237 ≤ 470286381) join_0_0 join_0_1

theorem join_1_1 : (twinPrimeSegment 470286381 470810669).card = 1709 := by
  simpa using combineTwinPrimeSegments (by decide : 470286381 ≤ 470548525)
    (by decide : 470548525 ≤ 470810669) join_0_2 join_0_3

theorem join_1_2 : (twinPrimeSegment 470810669 471334957).card = 1735 := by
  simpa using combineTwinPrimeSegments (by decide : 470810669 ≤ 471072813)
    (by decide : 471072813 ≤ 471334957) join_0_4 join_0_5

theorem join_1_3 : (twinPrimeSegment 471334957 471859245).card = 1794 := by
  simpa using combineTwinPrimeSegments (by decide : 471334957 ≤ 471597101)
    (by decide : 471597101 ≤ 471859245) join_0_6 join_0_7

theorem join_2_0 : (twinPrimeSegment 469762093 470810669).card = 3477 := by
  simpa using combineTwinPrimeSegments (by decide : 469762093 ≤ 470286381)
    (by decide : 470286381 ≤ 470810669) join_1_0 join_1_1

theorem join_2_1 : (twinPrimeSegment 470810669 471859245).card = 3529 := by
  simpa using combineTwinPrimeSegments (by decide : 470810669 ≤ 471334957)
    (by decide : 471334957 ≤ 471859245) join_1_2 join_1_3

theorem join_3_0 : (twinPrimeSegment 469762093 471859245).card = 7006 := by
  simpa using combineTwinPrimeSegments (by decide : 469762093 ≤ 470810669)
    (by decide : 470810669 ≤ 471859245) join_2_0 join_2_1

theorem total : (twinPrimeSegment 469762093 471859245).card = 7006 := join_3_0

end S224All
end Sude.GeneratedTwinScan
