import Sude.GeneratedTwinScan.S029C00
import Sude.GeneratedTwinScan.S029C01
import Sude.GeneratedTwinScan.S029C02
import Sude.GeneratedTwinScan.S029C03
import Sude.GeneratedTwinScan.S029C04
import Sude.GeneratedTwinScan.S029C05
import Sude.GeneratedTwinScan.S029C06
import Sude.GeneratedTwinScan.S029C07
import Sude.GeneratedTwinScan.S029C08
import Sude.GeneratedTwinScan.S029C09
import Sude.GeneratedTwinScan.S029C10
import Sude.GeneratedTwinScan.S029C11
import Sude.GeneratedTwinScan.S029C12
import Sude.GeneratedTwinScan.S029C13
import Sude.GeneratedTwinScan.S029C14
import Sude.GeneratedTwinScan.S029C15

/-! Combined FT source segment; Lean kernel check required. -/
namespace Sude.GeneratedTwinScan
namespace S029All

theorem join_0_0 : (twinPrimeSegment 60817453 61079597).card = 1099 := by
  simpa using combineTwinPrimeSegments (by decide : 60817453 ≤ 60948525)
    (by decide : 60948525 ≤ 61079597) S029C00.total S029C01.total

theorem join_0_1 : (twinPrimeSegment 61079597 61341741).card = 1038 := by
  simpa using combineTwinPrimeSegments (by decide : 61079597 ≤ 61210669)
    (by decide : 61210669 ≤ 61341741) S029C02.total S029C03.total

theorem join_0_2 : (twinPrimeSegment 61341741 61603885).card = 1081 := by
  simpa using combineTwinPrimeSegments (by decide : 61341741 ≤ 61472813)
    (by decide : 61472813 ≤ 61603885) S029C04.total S029C05.total

theorem join_0_3 : (twinPrimeSegment 61603885 61866029).card = 1118 := by
  simpa using combineTwinPrimeSegments (by decide : 61603885 ≤ 61734957)
    (by decide : 61734957 ≤ 61866029) S029C06.total S029C07.total

theorem join_0_4 : (twinPrimeSegment 61866029 62128173).card = 1044 := by
  simpa using combineTwinPrimeSegments (by decide : 61866029 ≤ 61997101)
    (by decide : 61997101 ≤ 62128173) S029C08.total S029C09.total

theorem join_0_5 : (twinPrimeSegment 62128173 62390317).card = 1034 := by
  simpa using combineTwinPrimeSegments (by decide : 62128173 ≤ 62259245)
    (by decide : 62259245 ≤ 62390317) S029C10.total S029C11.total

theorem join_0_6 : (twinPrimeSegment 62390317 62652461).card = 1003 := by
  simpa using combineTwinPrimeSegments (by decide : 62390317 ≤ 62521389)
    (by decide : 62521389 ≤ 62652461) S029C12.total S029C13.total

theorem join_0_7 : (twinPrimeSegment 62652461 62914605).card = 1081 := by
  simpa using combineTwinPrimeSegments (by decide : 62652461 ≤ 62783533)
    (by decide : 62783533 ≤ 62914605) S029C14.total S029C15.total

theorem join_1_0 : (twinPrimeSegment 60817453 61341741).card = 2137 := by
  simpa using combineTwinPrimeSegments (by decide : 60817453 ≤ 61079597)
    (by decide : 61079597 ≤ 61341741) join_0_0 join_0_1

theorem join_1_1 : (twinPrimeSegment 61341741 61866029).card = 2199 := by
  simpa using combineTwinPrimeSegments (by decide : 61341741 ≤ 61603885)
    (by decide : 61603885 ≤ 61866029) join_0_2 join_0_3

theorem join_1_2 : (twinPrimeSegment 61866029 62390317).card = 2078 := by
  simpa using combineTwinPrimeSegments (by decide : 61866029 ≤ 62128173)
    (by decide : 62128173 ≤ 62390317) join_0_4 join_0_5

theorem join_1_3 : (twinPrimeSegment 62390317 62914605).card = 2084 := by
  simpa using combineTwinPrimeSegments (by decide : 62390317 ≤ 62652461)
    (by decide : 62652461 ≤ 62914605) join_0_6 join_0_7

theorem join_2_0 : (twinPrimeSegment 60817453 61866029).card = 4336 := by
  simpa using combineTwinPrimeSegments (by decide : 60817453 ≤ 61341741)
    (by decide : 61341741 ≤ 61866029) join_1_0 join_1_1

theorem join_2_1 : (twinPrimeSegment 61866029 62914605).card = 4162 := by
  simpa using combineTwinPrimeSegments (by decide : 61866029 ≤ 62390317)
    (by decide : 62390317 ≤ 62914605) join_1_2 join_1_3

theorem join_3_0 : (twinPrimeSegment 60817453 62914605).card = 8498 := by
  simpa using combineTwinPrimeSegments (by decide : 60817453 ≤ 61866029)
    (by decide : 61866029 ≤ 62914605) join_2_0 join_2_1

theorem total : (twinPrimeSegment 60817453 62914605).card = 8498 := join_3_0

end S029All
end Sude.GeneratedTwinScan
