import Sude.GeneratedTwinScan.S063C00
import Sude.GeneratedTwinScan.S063C01
import Sude.GeneratedTwinScan.S063C02
import Sude.GeneratedTwinScan.S063C03
import Sude.GeneratedTwinScan.S063C04
import Sude.GeneratedTwinScan.S063C05
import Sude.GeneratedTwinScan.S063C06
import Sude.GeneratedTwinScan.S063C07
import Sude.GeneratedTwinScan.S063C08
import Sude.GeneratedTwinScan.S063C09
import Sude.GeneratedTwinScan.S063C10
import Sude.GeneratedTwinScan.S063C11
import Sude.GeneratedTwinScan.S063C12
import Sude.GeneratedTwinScan.S063C13
import Sude.GeneratedTwinScan.S063C14
import Sude.GeneratedTwinScan.S063C15

/-! Combined FT source segment; Lean kernel check required. -/
namespace Sude.GeneratedTwinScan
namespace S063All

theorem join_0_0 : (twinPrimeSegment 132120621 132382765).card = 980 := by
  simpa using combineTwinPrimeSegments (by decide : 132120621 ≤ 132251693)
    (by decide : 132251693 ≤ 132382765) S063C00.total S063C01.total

theorem join_0_1 : (twinPrimeSegment 132382765 132644909).card = 982 := by
  simpa using combineTwinPrimeSegments (by decide : 132382765 ≤ 132513837)
    (by decide : 132513837 ≤ 132644909) S063C02.total S063C03.total

theorem join_0_2 : (twinPrimeSegment 132644909 132907053).card = 992 := by
  simpa using combineTwinPrimeSegments (by decide : 132644909 ≤ 132775981)
    (by decide : 132775981 ≤ 132907053) S063C04.total S063C05.total

theorem join_0_3 : (twinPrimeSegment 132907053 133169197).card = 1009 := by
  simpa using combineTwinPrimeSegments (by decide : 132907053 ≤ 133038125)
    (by decide : 133038125 ≤ 133169197) S063C06.total S063C07.total

theorem join_0_4 : (twinPrimeSegment 133169197 133431341).card = 989 := by
  simpa using combineTwinPrimeSegments (by decide : 133169197 ≤ 133300269)
    (by decide : 133300269 ≤ 133431341) S063C08.total S063C09.total

theorem join_0_5 : (twinPrimeSegment 133431341 133693485).card = 982 := by
  simpa using combineTwinPrimeSegments (by decide : 133431341 ≤ 133562413)
    (by decide : 133562413 ≤ 133693485) S063C10.total S063C11.total

theorem join_0_6 : (twinPrimeSegment 133693485 133955629).card = 974 := by
  simpa using combineTwinPrimeSegments (by decide : 133693485 ≤ 133824557)
    (by decide : 133824557 ≤ 133955629) S063C12.total S063C13.total

theorem join_0_7 : (twinPrimeSegment 133955629 134217773).card = 991 := by
  simpa using combineTwinPrimeSegments (by decide : 133955629 ≤ 134086701)
    (by decide : 134086701 ≤ 134217773) S063C14.total S063C15.total

theorem join_1_0 : (twinPrimeSegment 132120621 132644909).card = 1962 := by
  simpa using combineTwinPrimeSegments (by decide : 132120621 ≤ 132382765)
    (by decide : 132382765 ≤ 132644909) join_0_0 join_0_1

theorem join_1_1 : (twinPrimeSegment 132644909 133169197).card = 2001 := by
  simpa using combineTwinPrimeSegments (by decide : 132644909 ≤ 132907053)
    (by decide : 132907053 ≤ 133169197) join_0_2 join_0_3

theorem join_1_2 : (twinPrimeSegment 133169197 133693485).card = 1971 := by
  simpa using combineTwinPrimeSegments (by decide : 133169197 ≤ 133431341)
    (by decide : 133431341 ≤ 133693485) join_0_4 join_0_5

theorem join_1_3 : (twinPrimeSegment 133693485 134217773).card = 1965 := by
  simpa using combineTwinPrimeSegments (by decide : 133693485 ≤ 133955629)
    (by decide : 133955629 ≤ 134217773) join_0_6 join_0_7

theorem join_2_0 : (twinPrimeSegment 132120621 133169197).card = 3963 := by
  simpa using combineTwinPrimeSegments (by decide : 132120621 ≤ 132644909)
    (by decide : 132644909 ≤ 133169197) join_1_0 join_1_1

theorem join_2_1 : (twinPrimeSegment 133169197 134217773).card = 3936 := by
  simpa using combineTwinPrimeSegments (by decide : 133169197 ≤ 133693485)
    (by decide : 133693485 ≤ 134217773) join_1_2 join_1_3

theorem join_3_0 : (twinPrimeSegment 132120621 134217773).card = 7899 := by
  simpa using combineTwinPrimeSegments (by decide : 132120621 ≤ 133169197)
    (by decide : 133169197 ≤ 134217773) join_2_0 join_2_1

theorem total : (twinPrimeSegment 132120621 134217773).card = 7899 := join_3_0

end S063All
end Sude.GeneratedTwinScan
