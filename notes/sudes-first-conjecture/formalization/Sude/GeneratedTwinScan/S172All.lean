import Sude.GeneratedTwinScan.S172C00
import Sude.GeneratedTwinScan.S172C01
import Sude.GeneratedTwinScan.S172C02
import Sude.GeneratedTwinScan.S172C03
import Sude.GeneratedTwinScan.S172C04
import Sude.GeneratedTwinScan.S172C05
import Sude.GeneratedTwinScan.S172C06
import Sude.GeneratedTwinScan.S172C07
import Sude.GeneratedTwinScan.S172C08
import Sude.GeneratedTwinScan.S172C09
import Sude.GeneratedTwinScan.S172C10
import Sude.GeneratedTwinScan.S172C11
import Sude.GeneratedTwinScan.S172C12
import Sude.GeneratedTwinScan.S172C13
import Sude.GeneratedTwinScan.S172C14
import Sude.GeneratedTwinScan.S172C15

/-! Combined FT source segment; Lean kernel check required. -/
namespace Sude.GeneratedTwinScan
namespace S172All

theorem join_0_0 : (twinPrimeSegment 360710189 360972333).card = 902 := by
  simpa using combineTwinPrimeSegments (by decide : 360710189 ≤ 360841261)
    (by decide : 360841261 ≤ 360972333) S172C00.total S172C01.total

theorem join_0_1 : (twinPrimeSegment 360972333 361234477).card = 874 := by
  simpa using combineTwinPrimeSegments (by decide : 360972333 ≤ 361103405)
    (by decide : 361103405 ≤ 361234477) S172C02.total S172C03.total

theorem join_0_2 : (twinPrimeSegment 361234477 361496621).card = 901 := by
  simpa using combineTwinPrimeSegments (by decide : 361234477 ≤ 361365549)
    (by decide : 361365549 ≤ 361496621) S172C04.total S172C05.total

theorem join_0_3 : (twinPrimeSegment 361496621 361758765).card = 899 := by
  simpa using combineTwinPrimeSegments (by decide : 361496621 ≤ 361627693)
    (by decide : 361627693 ≤ 361758765) S172C06.total S172C07.total

theorem join_0_4 : (twinPrimeSegment 361758765 362020909).card = 875 := by
  simpa using combineTwinPrimeSegments (by decide : 361758765 ≤ 361889837)
    (by decide : 361889837 ≤ 362020909) S172C08.total S172C09.total

theorem join_0_5 : (twinPrimeSegment 362020909 362283053).card = 895 := by
  simpa using combineTwinPrimeSegments (by decide : 362020909 ≤ 362151981)
    (by decide : 362151981 ≤ 362283053) S172C10.total S172C11.total

theorem join_0_6 : (twinPrimeSegment 362283053 362545197).card = 888 := by
  simpa using combineTwinPrimeSegments (by decide : 362283053 ≤ 362414125)
    (by decide : 362414125 ≤ 362545197) S172C12.total S172C13.total

theorem join_0_7 : (twinPrimeSegment 362545197 362807341).card = 859 := by
  simpa using combineTwinPrimeSegments (by decide : 362545197 ≤ 362676269)
    (by decide : 362676269 ≤ 362807341) S172C14.total S172C15.total

theorem join_1_0 : (twinPrimeSegment 360710189 361234477).card = 1776 := by
  simpa using combineTwinPrimeSegments (by decide : 360710189 ≤ 360972333)
    (by decide : 360972333 ≤ 361234477) join_0_0 join_0_1

theorem join_1_1 : (twinPrimeSegment 361234477 361758765).card = 1800 := by
  simpa using combineTwinPrimeSegments (by decide : 361234477 ≤ 361496621)
    (by decide : 361496621 ≤ 361758765) join_0_2 join_0_3

theorem join_1_2 : (twinPrimeSegment 361758765 362283053).card = 1770 := by
  simpa using combineTwinPrimeSegments (by decide : 361758765 ≤ 362020909)
    (by decide : 362020909 ≤ 362283053) join_0_4 join_0_5

theorem join_1_3 : (twinPrimeSegment 362283053 362807341).card = 1747 := by
  simpa using combineTwinPrimeSegments (by decide : 362283053 ≤ 362545197)
    (by decide : 362545197 ≤ 362807341) join_0_6 join_0_7

theorem join_2_0 : (twinPrimeSegment 360710189 361758765).card = 3576 := by
  simpa using combineTwinPrimeSegments (by decide : 360710189 ≤ 361234477)
    (by decide : 361234477 ≤ 361758765) join_1_0 join_1_1

theorem join_2_1 : (twinPrimeSegment 361758765 362807341).card = 3517 := by
  simpa using combineTwinPrimeSegments (by decide : 361758765 ≤ 362283053)
    (by decide : 362283053 ≤ 362807341) join_1_2 join_1_3

theorem join_3_0 : (twinPrimeSegment 360710189 362807341).card = 7093 := by
  simpa using combineTwinPrimeSegments (by decide : 360710189 ≤ 361758765)
    (by decide : 361758765 ≤ 362807341) join_2_0 join_2_1

theorem total : (twinPrimeSegment 360710189 362807341).card = 7093 := join_3_0

end S172All
end Sude.GeneratedTwinScan
