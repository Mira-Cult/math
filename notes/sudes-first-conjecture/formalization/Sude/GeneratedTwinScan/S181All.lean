import Sude.GeneratedTwinScan.S181C00
import Sude.GeneratedTwinScan.S181C01
import Sude.GeneratedTwinScan.S181C02
import Sude.GeneratedTwinScan.S181C03
import Sude.GeneratedTwinScan.S181C04
import Sude.GeneratedTwinScan.S181C05
import Sude.GeneratedTwinScan.S181C06
import Sude.GeneratedTwinScan.S181C07
import Sude.GeneratedTwinScan.S181C08
import Sude.GeneratedTwinScan.S181C09
import Sude.GeneratedTwinScan.S181C10
import Sude.GeneratedTwinScan.S181C11
import Sude.GeneratedTwinScan.S181C12
import Sude.GeneratedTwinScan.S181C13
import Sude.GeneratedTwinScan.S181C14
import Sude.GeneratedTwinScan.S181C15

/-! Combined FT source segment; Lean kernel check required. -/
namespace Sude.GeneratedTwinScan
namespace S181All

theorem join_0_0 : (twinPrimeSegment 379584557 379846701).card = 918 := by
  simpa using combineTwinPrimeSegments (by decide : 379584557 ≤ 379715629)
    (by decide : 379715629 ≤ 379846701) S181C00.total S181C01.total

theorem join_0_1 : (twinPrimeSegment 379846701 380108845).card = 885 := by
  simpa using combineTwinPrimeSegments (by decide : 379846701 ≤ 379977773)
    (by decide : 379977773 ≤ 380108845) S181C02.total S181C03.total

theorem join_0_2 : (twinPrimeSegment 380108845 380370989).card = 908 := by
  simpa using combineTwinPrimeSegments (by decide : 380108845 ≤ 380239917)
    (by decide : 380239917 ≤ 380370989) S181C04.total S181C05.total

theorem join_0_3 : (twinPrimeSegment 380370989 380633133).card = 907 := by
  simpa using combineTwinPrimeSegments (by decide : 380370989 ≤ 380502061)
    (by decide : 380502061 ≤ 380633133) S181C06.total S181C07.total

theorem join_0_4 : (twinPrimeSegment 380633133 380895277).card = 919 := by
  simpa using combineTwinPrimeSegments (by decide : 380633133 ≤ 380764205)
    (by decide : 380764205 ≤ 380895277) S181C08.total S181C09.total

theorem join_0_5 : (twinPrimeSegment 380895277 381157421).card = 880 := by
  simpa using combineTwinPrimeSegments (by decide : 380895277 ≤ 381026349)
    (by decide : 381026349 ≤ 381157421) S181C10.total S181C11.total

theorem join_0_6 : (twinPrimeSegment 381157421 381419565).card = 908 := by
  simpa using combineTwinPrimeSegments (by decide : 381157421 ≤ 381288493)
    (by decide : 381288493 ≤ 381419565) S181C12.total S181C13.total

theorem join_0_7 : (twinPrimeSegment 381419565 381681709).card = 896 := by
  simpa using combineTwinPrimeSegments (by decide : 381419565 ≤ 381550637)
    (by decide : 381550637 ≤ 381681709) S181C14.total S181C15.total

theorem join_1_0 : (twinPrimeSegment 379584557 380108845).card = 1803 := by
  simpa using combineTwinPrimeSegments (by decide : 379584557 ≤ 379846701)
    (by decide : 379846701 ≤ 380108845) join_0_0 join_0_1

theorem join_1_1 : (twinPrimeSegment 380108845 380633133).card = 1815 := by
  simpa using combineTwinPrimeSegments (by decide : 380108845 ≤ 380370989)
    (by decide : 380370989 ≤ 380633133) join_0_2 join_0_3

theorem join_1_2 : (twinPrimeSegment 380633133 381157421).card = 1799 := by
  simpa using combineTwinPrimeSegments (by decide : 380633133 ≤ 380895277)
    (by decide : 380895277 ≤ 381157421) join_0_4 join_0_5

theorem join_1_3 : (twinPrimeSegment 381157421 381681709).card = 1804 := by
  simpa using combineTwinPrimeSegments (by decide : 381157421 ≤ 381419565)
    (by decide : 381419565 ≤ 381681709) join_0_6 join_0_7

theorem join_2_0 : (twinPrimeSegment 379584557 380633133).card = 3618 := by
  simpa using combineTwinPrimeSegments (by decide : 379584557 ≤ 380108845)
    (by decide : 380108845 ≤ 380633133) join_1_0 join_1_1

theorem join_2_1 : (twinPrimeSegment 380633133 381681709).card = 3603 := by
  simpa using combineTwinPrimeSegments (by decide : 380633133 ≤ 381157421)
    (by decide : 381157421 ≤ 381681709) join_1_2 join_1_3

theorem join_3_0 : (twinPrimeSegment 379584557 381681709).card = 7221 := by
  simpa using combineTwinPrimeSegments (by decide : 379584557 ≤ 380633133)
    (by decide : 380633133 ≤ 381681709) join_2_0 join_2_1

theorem total : (twinPrimeSegment 379584557 381681709).card = 7221 := join_3_0

end S181All
end Sude.GeneratedTwinScan
