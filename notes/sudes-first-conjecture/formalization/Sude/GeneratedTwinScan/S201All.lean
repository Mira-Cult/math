import Sude.GeneratedTwinScan.S201C00
import Sude.GeneratedTwinScan.S201C01
import Sude.GeneratedTwinScan.S201C02
import Sude.GeneratedTwinScan.S201C03
import Sude.GeneratedTwinScan.S201C04
import Sude.GeneratedTwinScan.S201C05
import Sude.GeneratedTwinScan.S201C06
import Sude.GeneratedTwinScan.S201C07
import Sude.GeneratedTwinScan.S201C08
import Sude.GeneratedTwinScan.S201C09
import Sude.GeneratedTwinScan.S201C10
import Sude.GeneratedTwinScan.S201C11
import Sude.GeneratedTwinScan.S201C12
import Sude.GeneratedTwinScan.S201C13
import Sude.GeneratedTwinScan.S201C14
import Sude.GeneratedTwinScan.S201C15

/-! Combined FT source segment; Lean kernel check required. -/
namespace Sude.GeneratedTwinScan
namespace S201All

theorem join_0_0 : (twinPrimeSegment 421527597 421789741).card = 885 := by
  simpa using combineTwinPrimeSegments (by decide : 421527597 ≤ 421658669)
    (by decide : 421658669 ≤ 421789741) S201C00.total S201C01.total

theorem join_0_1 : (twinPrimeSegment 421789741 422051885).card = 898 := by
  simpa using combineTwinPrimeSegments (by decide : 421789741 ≤ 421920813)
    (by decide : 421920813 ≤ 422051885) S201C02.total S201C03.total

theorem join_0_2 : (twinPrimeSegment 422051885 422314029).card = 854 := by
  simpa using combineTwinPrimeSegments (by decide : 422051885 ≤ 422182957)
    (by decide : 422182957 ≤ 422314029) S201C04.total S201C05.total

theorem join_0_3 : (twinPrimeSegment 422314029 422576173).card = 890 := by
  simpa using combineTwinPrimeSegments (by decide : 422314029 ≤ 422445101)
    (by decide : 422445101 ≤ 422576173) S201C06.total S201C07.total

theorem join_0_4 : (twinPrimeSegment 422576173 422838317).card = 860 := by
  simpa using combineTwinPrimeSegments (by decide : 422576173 ≤ 422707245)
    (by decide : 422707245 ≤ 422838317) S201C08.total S201C09.total

theorem join_0_5 : (twinPrimeSegment 422838317 423100461).card = 875 := by
  simpa using combineTwinPrimeSegments (by decide : 422838317 ≤ 422969389)
    (by decide : 422969389 ≤ 423100461) S201C10.total S201C11.total

theorem join_0_6 : (twinPrimeSegment 423100461 423362605).card = 904 := by
  simpa using combineTwinPrimeSegments (by decide : 423100461 ≤ 423231533)
    (by decide : 423231533 ≤ 423362605) S201C12.total S201C13.total

theorem join_0_7 : (twinPrimeSegment 423362605 423624749).card = 875 := by
  simpa using combineTwinPrimeSegments (by decide : 423362605 ≤ 423493677)
    (by decide : 423493677 ≤ 423624749) S201C14.total S201C15.total

theorem join_1_0 : (twinPrimeSegment 421527597 422051885).card = 1783 := by
  simpa using combineTwinPrimeSegments (by decide : 421527597 ≤ 421789741)
    (by decide : 421789741 ≤ 422051885) join_0_0 join_0_1

theorem join_1_1 : (twinPrimeSegment 422051885 422576173).card = 1744 := by
  simpa using combineTwinPrimeSegments (by decide : 422051885 ≤ 422314029)
    (by decide : 422314029 ≤ 422576173) join_0_2 join_0_3

theorem join_1_2 : (twinPrimeSegment 422576173 423100461).card = 1735 := by
  simpa using combineTwinPrimeSegments (by decide : 422576173 ≤ 422838317)
    (by decide : 422838317 ≤ 423100461) join_0_4 join_0_5

theorem join_1_3 : (twinPrimeSegment 423100461 423624749).card = 1779 := by
  simpa using combineTwinPrimeSegments (by decide : 423100461 ≤ 423362605)
    (by decide : 423362605 ≤ 423624749) join_0_6 join_0_7

theorem join_2_0 : (twinPrimeSegment 421527597 422576173).card = 3527 := by
  simpa using combineTwinPrimeSegments (by decide : 421527597 ≤ 422051885)
    (by decide : 422051885 ≤ 422576173) join_1_0 join_1_1

theorem join_2_1 : (twinPrimeSegment 422576173 423624749).card = 3514 := by
  simpa using combineTwinPrimeSegments (by decide : 422576173 ≤ 423100461)
    (by decide : 423100461 ≤ 423624749) join_1_2 join_1_3

theorem join_3_0 : (twinPrimeSegment 421527597 423624749).card = 7041 := by
  simpa using combineTwinPrimeSegments (by decide : 421527597 ≤ 422576173)
    (by decide : 422576173 ≤ 423624749) join_2_0 join_2_1

theorem total : (twinPrimeSegment 421527597 423624749).card = 7041 := join_3_0

end S201All
end Sude.GeneratedTwinScan
