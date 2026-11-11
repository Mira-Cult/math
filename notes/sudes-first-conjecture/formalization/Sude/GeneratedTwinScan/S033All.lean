import Sude.GeneratedTwinScan.S033C00
import Sude.GeneratedTwinScan.S033C01
import Sude.GeneratedTwinScan.S033C02
import Sude.GeneratedTwinScan.S033C03
import Sude.GeneratedTwinScan.S033C04
import Sude.GeneratedTwinScan.S033C05
import Sude.GeneratedTwinScan.S033C06
import Sude.GeneratedTwinScan.S033C07
import Sude.GeneratedTwinScan.S033C08
import Sude.GeneratedTwinScan.S033C09
import Sude.GeneratedTwinScan.S033C10
import Sude.GeneratedTwinScan.S033C11
import Sude.GeneratedTwinScan.S033C12
import Sude.GeneratedTwinScan.S033C13
import Sude.GeneratedTwinScan.S033C14
import Sude.GeneratedTwinScan.S033C15

/-! Combined FT source segment; Lean kernel check required. -/
namespace Sude.GeneratedTwinScan
namespace S033All

theorem join_0_0 : (twinPrimeSegment 69206061 69468205).card = 1093 := by
  simpa using combineTwinPrimeSegments (by decide : 69206061 ≤ 69337133)
    (by decide : 69337133 ≤ 69468205) S033C00.total S033C01.total

theorem join_0_1 : (twinPrimeSegment 69468205 69730349).card = 1093 := by
  simpa using combineTwinPrimeSegments (by decide : 69468205 ≤ 69599277)
    (by decide : 69599277 ≤ 69730349) S033C02.total S033C03.total

theorem join_0_2 : (twinPrimeSegment 69730349 69992493).card = 1067 := by
  simpa using combineTwinPrimeSegments (by decide : 69730349 ≤ 69861421)
    (by decide : 69861421 ≤ 69992493) S033C04.total S033C05.total

theorem join_0_3 : (twinPrimeSegment 69992493 70254637).card = 1061 := by
  simpa using combineTwinPrimeSegments (by decide : 69992493 ≤ 70123565)
    (by decide : 70123565 ≤ 70254637) S033C06.total S033C07.total

theorem join_0_4 : (twinPrimeSegment 70254637 70516781).card = 1059 := by
  simpa using combineTwinPrimeSegments (by decide : 70254637 ≤ 70385709)
    (by decide : 70385709 ≤ 70516781) S033C08.total S033C09.total

theorem join_0_5 : (twinPrimeSegment 70516781 70778925).card = 1070 := by
  simpa using combineTwinPrimeSegments (by decide : 70516781 ≤ 70647853)
    (by decide : 70647853 ≤ 70778925) S033C10.total S033C11.total

theorem join_0_6 : (twinPrimeSegment 70778925 71041069).card = 974 := by
  simpa using combineTwinPrimeSegments (by decide : 70778925 ≤ 70909997)
    (by decide : 70909997 ≤ 71041069) S033C12.total S033C13.total

theorem join_0_7 : (twinPrimeSegment 71041069 71303213).card = 1077 := by
  simpa using combineTwinPrimeSegments (by decide : 71041069 ≤ 71172141)
    (by decide : 71172141 ≤ 71303213) S033C14.total S033C15.total

theorem join_1_0 : (twinPrimeSegment 69206061 69730349).card = 2186 := by
  simpa using combineTwinPrimeSegments (by decide : 69206061 ≤ 69468205)
    (by decide : 69468205 ≤ 69730349) join_0_0 join_0_1

theorem join_1_1 : (twinPrimeSegment 69730349 70254637).card = 2128 := by
  simpa using combineTwinPrimeSegments (by decide : 69730349 ≤ 69992493)
    (by decide : 69992493 ≤ 70254637) join_0_2 join_0_3

theorem join_1_2 : (twinPrimeSegment 70254637 70778925).card = 2129 := by
  simpa using combineTwinPrimeSegments (by decide : 70254637 ≤ 70516781)
    (by decide : 70516781 ≤ 70778925) join_0_4 join_0_5

theorem join_1_3 : (twinPrimeSegment 70778925 71303213).card = 2051 := by
  simpa using combineTwinPrimeSegments (by decide : 70778925 ≤ 71041069)
    (by decide : 71041069 ≤ 71303213) join_0_6 join_0_7

theorem join_2_0 : (twinPrimeSegment 69206061 70254637).card = 4314 := by
  simpa using combineTwinPrimeSegments (by decide : 69206061 ≤ 69730349)
    (by decide : 69730349 ≤ 70254637) join_1_0 join_1_1

theorem join_2_1 : (twinPrimeSegment 70254637 71303213).card = 4180 := by
  simpa using combineTwinPrimeSegments (by decide : 70254637 ≤ 70778925)
    (by decide : 70778925 ≤ 71303213) join_1_2 join_1_3

theorem join_3_0 : (twinPrimeSegment 69206061 71303213).card = 8494 := by
  simpa using combineTwinPrimeSegments (by decide : 69206061 ≤ 70254637)
    (by decide : 70254637 ≤ 71303213) join_2_0 join_2_1

theorem total : (twinPrimeSegment 69206061 71303213).card = 8494 := join_3_0

end S033All
end Sude.GeneratedTwinScan
