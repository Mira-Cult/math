import Sude.GeneratedTwinScan.S188C00
import Sude.GeneratedTwinScan.S188C01
import Sude.GeneratedTwinScan.S188C02
import Sude.GeneratedTwinScan.S188C03
import Sude.GeneratedTwinScan.S188C04
import Sude.GeneratedTwinScan.S188C05
import Sude.GeneratedTwinScan.S188C06
import Sude.GeneratedTwinScan.S188C07
import Sude.GeneratedTwinScan.S188C08
import Sude.GeneratedTwinScan.S188C09
import Sude.GeneratedTwinScan.S188C10
import Sude.GeneratedTwinScan.S188C11
import Sude.GeneratedTwinScan.S188C12
import Sude.GeneratedTwinScan.S188C13
import Sude.GeneratedTwinScan.S188C14
import Sude.GeneratedTwinScan.S188C15

/-! Combined FT source segment; Lean kernel check required. -/
namespace Sude.GeneratedTwinScan
namespace S188All

theorem join_0_0 : (twinPrimeSegment 394264621 394526765).card = 865 := by
  simpa using combineTwinPrimeSegments (by decide : 394264621 ≤ 394395693)
    (by decide : 394395693 ≤ 394526765) S188C00.total S188C01.total

theorem join_0_1 : (twinPrimeSegment 394526765 394788909).card = 902 := by
  simpa using combineTwinPrimeSegments (by decide : 394526765 ≤ 394657837)
    (by decide : 394657837 ≤ 394788909) S188C02.total S188C03.total

theorem join_0_2 : (twinPrimeSegment 394788909 395051053).card = 897 := by
  simpa using combineTwinPrimeSegments (by decide : 394788909 ≤ 394919981)
    (by decide : 394919981 ≤ 395051053) S188C04.total S188C05.total

theorem join_0_3 : (twinPrimeSegment 395051053 395313197).card = 905 := by
  simpa using combineTwinPrimeSegments (by decide : 395051053 ≤ 395182125)
    (by decide : 395182125 ≤ 395313197) S188C06.total S188C07.total

theorem join_0_4 : (twinPrimeSegment 395313197 395575341).card = 856 := by
  simpa using combineTwinPrimeSegments (by decide : 395313197 ≤ 395444269)
    (by decide : 395444269 ≤ 395575341) S188C08.total S188C09.total

theorem join_0_5 : (twinPrimeSegment 395575341 395837485).card = 866 := by
  simpa using combineTwinPrimeSegments (by decide : 395575341 ≤ 395706413)
    (by decide : 395706413 ≤ 395837485) S188C10.total S188C11.total

theorem join_0_6 : (twinPrimeSegment 395837485 396099629).card = 872 := by
  simpa using combineTwinPrimeSegments (by decide : 395837485 ≤ 395968557)
    (by decide : 395968557 ≤ 396099629) S188C12.total S188C13.total

theorem join_0_7 : (twinPrimeSegment 396099629 396361773).card = 875 := by
  simpa using combineTwinPrimeSegments (by decide : 396099629 ≤ 396230701)
    (by decide : 396230701 ≤ 396361773) S188C14.total S188C15.total

theorem join_1_0 : (twinPrimeSegment 394264621 394788909).card = 1767 := by
  simpa using combineTwinPrimeSegments (by decide : 394264621 ≤ 394526765)
    (by decide : 394526765 ≤ 394788909) join_0_0 join_0_1

theorem join_1_1 : (twinPrimeSegment 394788909 395313197).card = 1802 := by
  simpa using combineTwinPrimeSegments (by decide : 394788909 ≤ 395051053)
    (by decide : 395051053 ≤ 395313197) join_0_2 join_0_3

theorem join_1_2 : (twinPrimeSegment 395313197 395837485).card = 1722 := by
  simpa using combineTwinPrimeSegments (by decide : 395313197 ≤ 395575341)
    (by decide : 395575341 ≤ 395837485) join_0_4 join_0_5

theorem join_1_3 : (twinPrimeSegment 395837485 396361773).card = 1747 := by
  simpa using combineTwinPrimeSegments (by decide : 395837485 ≤ 396099629)
    (by decide : 396099629 ≤ 396361773) join_0_6 join_0_7

theorem join_2_0 : (twinPrimeSegment 394264621 395313197).card = 3569 := by
  simpa using combineTwinPrimeSegments (by decide : 394264621 ≤ 394788909)
    (by decide : 394788909 ≤ 395313197) join_1_0 join_1_1

theorem join_2_1 : (twinPrimeSegment 395313197 396361773).card = 3469 := by
  simpa using combineTwinPrimeSegments (by decide : 395313197 ≤ 395837485)
    (by decide : 395837485 ≤ 396361773) join_1_2 join_1_3

theorem join_3_0 : (twinPrimeSegment 394264621 396361773).card = 7038 := by
  simpa using combineTwinPrimeSegments (by decide : 394264621 ≤ 395313197)
    (by decide : 395313197 ≤ 396361773) join_2_0 join_2_1

theorem total : (twinPrimeSegment 394264621 396361773).card = 7038 := join_3_0

end S188All
end Sude.GeneratedTwinScan
