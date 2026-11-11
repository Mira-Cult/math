import Sude.GeneratedTwinScan.S022C00
import Sude.GeneratedTwinScan.S022C01
import Sude.GeneratedTwinScan.S022C02
import Sude.GeneratedTwinScan.S022C03
import Sude.GeneratedTwinScan.S022C04
import Sude.GeneratedTwinScan.S022C05
import Sude.GeneratedTwinScan.S022C06
import Sude.GeneratedTwinScan.S022C07
import Sude.GeneratedTwinScan.S022C08
import Sude.GeneratedTwinScan.S022C09
import Sude.GeneratedTwinScan.S022C10
import Sude.GeneratedTwinScan.S022C11
import Sude.GeneratedTwinScan.S022C12
import Sude.GeneratedTwinScan.S022C13
import Sude.GeneratedTwinScan.S022C14
import Sude.GeneratedTwinScan.S022C15

/-! Combined FT source segment; Lean kernel check required. -/
namespace Sude.GeneratedTwinScan
namespace S022All

theorem join_0_0 : (twinPrimeSegment 46137389 46399533).card = 1121 := by
  simpa using combineTwinPrimeSegments (by decide : 46137389 ≤ 46268461)
    (by decide : 46268461 ≤ 46399533) S022C00.total S022C01.total

theorem join_0_1 : (twinPrimeSegment 46399533 46661677).card = 1149 := by
  simpa using combineTwinPrimeSegments (by decide : 46399533 ≤ 46530605)
    (by decide : 46530605 ≤ 46661677) S022C02.total S022C03.total

theorem join_0_2 : (twinPrimeSegment 46661677 46923821).card = 1069 := by
  simpa using combineTwinPrimeSegments (by decide : 46661677 ≤ 46792749)
    (by decide : 46792749 ≤ 46923821) S022C04.total S022C05.total

theorem join_0_3 : (twinPrimeSegment 46923821 47185965).card = 1098 := by
  simpa using combineTwinPrimeSegments (by decide : 46923821 ≤ 47054893)
    (by decide : 47054893 ≤ 47185965) S022C06.total S022C07.total

theorem join_0_4 : (twinPrimeSegment 47185965 47448109).card = 1094 := by
  simpa using combineTwinPrimeSegments (by decide : 47185965 ≤ 47317037)
    (by decide : 47317037 ≤ 47448109) S022C08.total S022C09.total

theorem join_0_5 : (twinPrimeSegment 47448109 47710253).card = 1100 := by
  simpa using combineTwinPrimeSegments (by decide : 47448109 ≤ 47579181)
    (by decide : 47579181 ≤ 47710253) S022C10.total S022C11.total

theorem join_0_6 : (twinPrimeSegment 47710253 47972397).card = 1116 := by
  simpa using combineTwinPrimeSegments (by decide : 47710253 ≤ 47841325)
    (by decide : 47841325 ≤ 47972397) S022C12.total S022C13.total

theorem join_0_7 : (twinPrimeSegment 47972397 48234541).card = 1078 := by
  simpa using combineTwinPrimeSegments (by decide : 47972397 ≤ 48103469)
    (by decide : 48103469 ≤ 48234541) S022C14.total S022C15.total

theorem join_1_0 : (twinPrimeSegment 46137389 46661677).card = 2270 := by
  simpa using combineTwinPrimeSegments (by decide : 46137389 ≤ 46399533)
    (by decide : 46399533 ≤ 46661677) join_0_0 join_0_1

theorem join_1_1 : (twinPrimeSegment 46661677 47185965).card = 2167 := by
  simpa using combineTwinPrimeSegments (by decide : 46661677 ≤ 46923821)
    (by decide : 46923821 ≤ 47185965) join_0_2 join_0_3

theorem join_1_2 : (twinPrimeSegment 47185965 47710253).card = 2194 := by
  simpa using combineTwinPrimeSegments (by decide : 47185965 ≤ 47448109)
    (by decide : 47448109 ≤ 47710253) join_0_4 join_0_5

theorem join_1_3 : (twinPrimeSegment 47710253 48234541).card = 2194 := by
  simpa using combineTwinPrimeSegments (by decide : 47710253 ≤ 47972397)
    (by decide : 47972397 ≤ 48234541) join_0_6 join_0_7

theorem join_2_0 : (twinPrimeSegment 46137389 47185965).card = 4437 := by
  simpa using combineTwinPrimeSegments (by decide : 46137389 ≤ 46661677)
    (by decide : 46661677 ≤ 47185965) join_1_0 join_1_1

theorem join_2_1 : (twinPrimeSegment 47185965 48234541).card = 4388 := by
  simpa using combineTwinPrimeSegments (by decide : 47185965 ≤ 47710253)
    (by decide : 47710253 ≤ 48234541) join_1_2 join_1_3

theorem join_3_0 : (twinPrimeSegment 46137389 48234541).card = 8825 := by
  simpa using combineTwinPrimeSegments (by decide : 46137389 ≤ 47185965)
    (by decide : 47185965 ≤ 48234541) join_2_0 join_2_1

theorem total : (twinPrimeSegment 46137389 48234541).card = 8825 := join_3_0

end S022All
end Sude.GeneratedTwinScan
