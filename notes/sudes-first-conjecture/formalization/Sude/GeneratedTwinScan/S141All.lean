import Sude.GeneratedTwinScan.S141C00
import Sude.GeneratedTwinScan.S141C01
import Sude.GeneratedTwinScan.S141C02
import Sude.GeneratedTwinScan.S141C03
import Sude.GeneratedTwinScan.S141C04
import Sude.GeneratedTwinScan.S141C05
import Sude.GeneratedTwinScan.S141C06
import Sude.GeneratedTwinScan.S141C07
import Sude.GeneratedTwinScan.S141C08
import Sude.GeneratedTwinScan.S141C09
import Sude.GeneratedTwinScan.S141C10
import Sude.GeneratedTwinScan.S141C11
import Sude.GeneratedTwinScan.S141C12
import Sude.GeneratedTwinScan.S141C13
import Sude.GeneratedTwinScan.S141C14
import Sude.GeneratedTwinScan.S141C15

/-! Combined FT source segment; Lean kernel check required. -/
namespace Sude.GeneratedTwinScan
namespace S141All

theorem join_0_0 : (twinPrimeSegment 295698477 295960621).card = 889 := by
  simpa using combineTwinPrimeSegments (by decide : 295698477 ≤ 295829549)
    (by decide : 295829549 ≤ 295960621) S141C00.total S141C01.total

theorem join_0_1 : (twinPrimeSegment 295960621 296222765).card = 903 := by
  simpa using combineTwinPrimeSegments (by decide : 295960621 ≤ 296091693)
    (by decide : 296091693 ≤ 296222765) S141C02.total S141C03.total

theorem join_0_2 : (twinPrimeSegment 296222765 296484909).card = 895 := by
  simpa using combineTwinPrimeSegments (by decide : 296222765 ≤ 296353837)
    (by decide : 296353837 ≤ 296484909) S141C04.total S141C05.total

theorem join_0_3 : (twinPrimeSegment 296484909 296747053).card = 855 := by
  simpa using combineTwinPrimeSegments (by decide : 296484909 ≤ 296615981)
    (by decide : 296615981 ≤ 296747053) S141C06.total S141C07.total

theorem join_0_4 : (twinPrimeSegment 296747053 297009197).card = 909 := by
  simpa using combineTwinPrimeSegments (by decide : 296747053 ≤ 296878125)
    (by decide : 296878125 ≤ 297009197) S141C08.total S141C09.total

theorem join_0_5 : (twinPrimeSegment 297009197 297271341).card = 916 := by
  simpa using combineTwinPrimeSegments (by decide : 297009197 ≤ 297140269)
    (by decide : 297140269 ≤ 297271341) S141C10.total S141C11.total

theorem join_0_6 : (twinPrimeSegment 297271341 297533485).card = 922 := by
  simpa using combineTwinPrimeSegments (by decide : 297271341 ≤ 297402413)
    (by decide : 297402413 ≤ 297533485) S141C12.total S141C13.total

theorem join_0_7 : (twinPrimeSegment 297533485 297795629).card = 934 := by
  simpa using combineTwinPrimeSegments (by decide : 297533485 ≤ 297664557)
    (by decide : 297664557 ≤ 297795629) S141C14.total S141C15.total

theorem join_1_0 : (twinPrimeSegment 295698477 296222765).card = 1792 := by
  simpa using combineTwinPrimeSegments (by decide : 295698477 ≤ 295960621)
    (by decide : 295960621 ≤ 296222765) join_0_0 join_0_1

theorem join_1_1 : (twinPrimeSegment 296222765 296747053).card = 1750 := by
  simpa using combineTwinPrimeSegments (by decide : 296222765 ≤ 296484909)
    (by decide : 296484909 ≤ 296747053) join_0_2 join_0_3

theorem join_1_2 : (twinPrimeSegment 296747053 297271341).card = 1825 := by
  simpa using combineTwinPrimeSegments (by decide : 296747053 ≤ 297009197)
    (by decide : 297009197 ≤ 297271341) join_0_4 join_0_5

theorem join_1_3 : (twinPrimeSegment 297271341 297795629).card = 1856 := by
  simpa using combineTwinPrimeSegments (by decide : 297271341 ≤ 297533485)
    (by decide : 297533485 ≤ 297795629) join_0_6 join_0_7

theorem join_2_0 : (twinPrimeSegment 295698477 296747053).card = 3542 := by
  simpa using combineTwinPrimeSegments (by decide : 295698477 ≤ 296222765)
    (by decide : 296222765 ≤ 296747053) join_1_0 join_1_1

theorem join_2_1 : (twinPrimeSegment 296747053 297795629).card = 3681 := by
  simpa using combineTwinPrimeSegments (by decide : 296747053 ≤ 297271341)
    (by decide : 297271341 ≤ 297795629) join_1_2 join_1_3

theorem join_3_0 : (twinPrimeSegment 295698477 297795629).card = 7223 := by
  simpa using combineTwinPrimeSegments (by decide : 295698477 ≤ 296747053)
    (by decide : 296747053 ≤ 297795629) join_2_0 join_2_1

theorem total : (twinPrimeSegment 295698477 297795629).card = 7223 := join_3_0

end S141All
end Sude.GeneratedTwinScan
