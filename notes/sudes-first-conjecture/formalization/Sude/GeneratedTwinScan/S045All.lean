import Sude.GeneratedTwinScan.S045C00
import Sude.GeneratedTwinScan.S045C01
import Sude.GeneratedTwinScan.S045C02
import Sude.GeneratedTwinScan.S045C03
import Sude.GeneratedTwinScan.S045C04
import Sude.GeneratedTwinScan.S045C05
import Sude.GeneratedTwinScan.S045C06
import Sude.GeneratedTwinScan.S045C07
import Sude.GeneratedTwinScan.S045C08
import Sude.GeneratedTwinScan.S045C09
import Sude.GeneratedTwinScan.S045C10
import Sude.GeneratedTwinScan.S045C11
import Sude.GeneratedTwinScan.S045C12
import Sude.GeneratedTwinScan.S045C13
import Sude.GeneratedTwinScan.S045C14
import Sude.GeneratedTwinScan.S045C15

/-! Combined FT source segment; Lean kernel check required. -/
namespace Sude.GeneratedTwinScan
namespace S045All

theorem join_0_0 : (twinPrimeSegment 94371885 94634029).card = 1029 := by
  simpa using combineTwinPrimeSegments (by decide : 94371885 ≤ 94502957)
    (by decide : 94502957 ≤ 94634029) S045C00.total S045C01.total

theorem join_0_1 : (twinPrimeSegment 94634029 94896173).card = 1059 := by
  simpa using combineTwinPrimeSegments (by decide : 94634029 ≤ 94765101)
    (by decide : 94765101 ≤ 94896173) S045C02.total S045C03.total

theorem join_0_2 : (twinPrimeSegment 94896173 95158317).card = 945 := by
  simpa using combineTwinPrimeSegments (by decide : 94896173 ≤ 95027245)
    (by decide : 95027245 ≤ 95158317) S045C04.total S045C05.total

theorem join_0_3 : (twinPrimeSegment 95158317 95420461).card = 1033 := by
  simpa using combineTwinPrimeSegments (by decide : 95158317 ≤ 95289389)
    (by decide : 95289389 ≤ 95420461) S045C06.total S045C07.total

theorem join_0_4 : (twinPrimeSegment 95420461 95682605).card = 1039 := by
  simpa using combineTwinPrimeSegments (by decide : 95420461 ≤ 95551533)
    (by decide : 95551533 ≤ 95682605) S045C08.total S045C09.total

theorem join_0_5 : (twinPrimeSegment 95682605 95944749).card = 1022 := by
  simpa using combineTwinPrimeSegments (by decide : 95682605 ≤ 95813677)
    (by decide : 95813677 ≤ 95944749) S045C10.total S045C11.total

theorem join_0_6 : (twinPrimeSegment 95944749 96206893).card = 1019 := by
  simpa using combineTwinPrimeSegments (by decide : 95944749 ≤ 96075821)
    (by decide : 96075821 ≤ 96206893) S045C12.total S045C13.total

theorem join_0_7 : (twinPrimeSegment 96206893 96469037).card = 1052 := by
  simpa using combineTwinPrimeSegments (by decide : 96206893 ≤ 96337965)
    (by decide : 96337965 ≤ 96469037) S045C14.total S045C15.total

theorem join_1_0 : (twinPrimeSegment 94371885 94896173).card = 2088 := by
  simpa using combineTwinPrimeSegments (by decide : 94371885 ≤ 94634029)
    (by decide : 94634029 ≤ 94896173) join_0_0 join_0_1

theorem join_1_1 : (twinPrimeSegment 94896173 95420461).card = 1978 := by
  simpa using combineTwinPrimeSegments (by decide : 94896173 ≤ 95158317)
    (by decide : 95158317 ≤ 95420461) join_0_2 join_0_3

theorem join_1_2 : (twinPrimeSegment 95420461 95944749).card = 2061 := by
  simpa using combineTwinPrimeSegments (by decide : 95420461 ≤ 95682605)
    (by decide : 95682605 ≤ 95944749) join_0_4 join_0_5

theorem join_1_3 : (twinPrimeSegment 95944749 96469037).card = 2071 := by
  simpa using combineTwinPrimeSegments (by decide : 95944749 ≤ 96206893)
    (by decide : 96206893 ≤ 96469037) join_0_6 join_0_7

theorem join_2_0 : (twinPrimeSegment 94371885 95420461).card = 4066 := by
  simpa using combineTwinPrimeSegments (by decide : 94371885 ≤ 94896173)
    (by decide : 94896173 ≤ 95420461) join_1_0 join_1_1

theorem join_2_1 : (twinPrimeSegment 95420461 96469037).card = 4132 := by
  simpa using combineTwinPrimeSegments (by decide : 95420461 ≤ 95944749)
    (by decide : 95944749 ≤ 96469037) join_1_2 join_1_3

theorem join_3_0 : (twinPrimeSegment 94371885 96469037).card = 8198 := by
  simpa using combineTwinPrimeSegments (by decide : 94371885 ≤ 95420461)
    (by decide : 95420461 ≤ 96469037) join_2_0 join_2_1

theorem total : (twinPrimeSegment 94371885 96469037).card = 8198 := join_3_0

end S045All
end Sude.GeneratedTwinScan
