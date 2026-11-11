import Sude.GeneratedTwinScan.S014C00
import Sude.GeneratedTwinScan.S014C01
import Sude.GeneratedTwinScan.S014C02
import Sude.GeneratedTwinScan.S014C03
import Sude.GeneratedTwinScan.S014C04
import Sude.GeneratedTwinScan.S014C05
import Sude.GeneratedTwinScan.S014C06
import Sude.GeneratedTwinScan.S014C07
import Sude.GeneratedTwinScan.S014C08
import Sude.GeneratedTwinScan.S014C09
import Sude.GeneratedTwinScan.S014C10
import Sude.GeneratedTwinScan.S014C11
import Sude.GeneratedTwinScan.S014C12
import Sude.GeneratedTwinScan.S014C13
import Sude.GeneratedTwinScan.S014C14
import Sude.GeneratedTwinScan.S014C15

/-! Combined FT source segment; Lean kernel check required. -/
namespace Sude.GeneratedTwinScan
namespace S014All

theorem join_0_0 : (twinPrimeSegment 29360173 29622317).card = 1139 := by
  simpa using combineTwinPrimeSegments (by decide : 29360173 ≤ 29491245)
    (by decide : 29491245 ≤ 29622317) S014C00.total S014C01.total

theorem join_0_1 : (twinPrimeSegment 29622317 29884461).card = 1132 := by
  simpa using combineTwinPrimeSegments (by decide : 29622317 ≤ 29753389)
    (by decide : 29753389 ≤ 29884461) S014C02.total S014C03.total

theorem join_0_2 : (twinPrimeSegment 29884461 30146605).card = 1216 := by
  simpa using combineTwinPrimeSegments (by decide : 29884461 ≤ 30015533)
    (by decide : 30015533 ≤ 30146605) S014C04.total S014C05.total

theorem join_0_3 : (twinPrimeSegment 30146605 30408749).card = 1214 := by
  simpa using combineTwinPrimeSegments (by decide : 30146605 ≤ 30277677)
    (by decide : 30277677 ≤ 30408749) S014C06.total S014C07.total

theorem join_0_4 : (twinPrimeSegment 30408749 30670893).card = 1145 := by
  simpa using combineTwinPrimeSegments (by decide : 30408749 ≤ 30539821)
    (by decide : 30539821 ≤ 30670893) S014C08.total S014C09.total

theorem join_0_5 : (twinPrimeSegment 30670893 30933037).card = 1175 := by
  simpa using combineTwinPrimeSegments (by decide : 30670893 ≤ 30801965)
    (by decide : 30801965 ≤ 30933037) S014C10.total S014C11.total

theorem join_0_6 : (twinPrimeSegment 30933037 31195181).card = 1159 := by
  simpa using combineTwinPrimeSegments (by decide : 30933037 ≤ 31064109)
    (by decide : 31064109 ≤ 31195181) S014C12.total S014C13.total

theorem join_0_7 : (twinPrimeSegment 31195181 31457325).card = 1154 := by
  simpa using combineTwinPrimeSegments (by decide : 31195181 ≤ 31326253)
    (by decide : 31326253 ≤ 31457325) S014C14.total S014C15.total

theorem join_1_0 : (twinPrimeSegment 29360173 29884461).card = 2271 := by
  simpa using combineTwinPrimeSegments (by decide : 29360173 ≤ 29622317)
    (by decide : 29622317 ≤ 29884461) join_0_0 join_0_1

theorem join_1_1 : (twinPrimeSegment 29884461 30408749).card = 2430 := by
  simpa using combineTwinPrimeSegments (by decide : 29884461 ≤ 30146605)
    (by decide : 30146605 ≤ 30408749) join_0_2 join_0_3

theorem join_1_2 : (twinPrimeSegment 30408749 30933037).card = 2320 := by
  simpa using combineTwinPrimeSegments (by decide : 30408749 ≤ 30670893)
    (by decide : 30670893 ≤ 30933037) join_0_4 join_0_5

theorem join_1_3 : (twinPrimeSegment 30933037 31457325).card = 2313 := by
  simpa using combineTwinPrimeSegments (by decide : 30933037 ≤ 31195181)
    (by decide : 31195181 ≤ 31457325) join_0_6 join_0_7

theorem join_2_0 : (twinPrimeSegment 29360173 30408749).card = 4701 := by
  simpa using combineTwinPrimeSegments (by decide : 29360173 ≤ 29884461)
    (by decide : 29884461 ≤ 30408749) join_1_0 join_1_1

theorem join_2_1 : (twinPrimeSegment 30408749 31457325).card = 4633 := by
  simpa using combineTwinPrimeSegments (by decide : 30408749 ≤ 30933037)
    (by decide : 30933037 ≤ 31457325) join_1_2 join_1_3

theorem join_3_0 : (twinPrimeSegment 29360173 31457325).card = 9334 := by
  simpa using combineTwinPrimeSegments (by decide : 29360173 ≤ 30408749)
    (by decide : 30408749 ≤ 31457325) join_2_0 join_2_1

theorem total : (twinPrimeSegment 29360173 31457325).card = 9334 := join_3_0

end S014All
end Sude.GeneratedTwinScan
