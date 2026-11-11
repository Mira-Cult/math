import Sude.GeneratedTwinScan.S016C00
import Sude.GeneratedTwinScan.S016C01
import Sude.GeneratedTwinScan.S016C02
import Sude.GeneratedTwinScan.S016C03
import Sude.GeneratedTwinScan.S016C04
import Sude.GeneratedTwinScan.S016C05
import Sude.GeneratedTwinScan.S016C06
import Sude.GeneratedTwinScan.S016C07
import Sude.GeneratedTwinScan.S016C08
import Sude.GeneratedTwinScan.S016C09
import Sude.GeneratedTwinScan.S016C10
import Sude.GeneratedTwinScan.S016C11
import Sude.GeneratedTwinScan.S016C12
import Sude.GeneratedTwinScan.S016C13
import Sude.GeneratedTwinScan.S016C14
import Sude.GeneratedTwinScan.S016C15

/-! Combined FT source segment; Lean kernel check required. -/
namespace Sude.GeneratedTwinScan
namespace S016All

theorem join_0_0 : (twinPrimeSegment 33554477 33816621).card = 1148 := by
  simpa using combineTwinPrimeSegments (by decide : 33554477 ≤ 33685549)
    (by decide : 33685549 ≤ 33816621) S016C00.total S016C01.total

theorem join_0_1 : (twinPrimeSegment 33816621 34078765).card = 1159 := by
  simpa using combineTwinPrimeSegments (by decide : 33816621 ≤ 33947693)
    (by decide : 33947693 ≤ 34078765) S016C02.total S016C03.total

theorem join_0_2 : (twinPrimeSegment 34078765 34340909).card = 1123 := by
  simpa using combineTwinPrimeSegments (by decide : 34078765 ≤ 34209837)
    (by decide : 34209837 ≤ 34340909) S016C04.total S016C05.total

theorem join_0_3 : (twinPrimeSegment 34340909 34603053).card = 1166 := by
  simpa using combineTwinPrimeSegments (by decide : 34340909 ≤ 34471981)
    (by decide : 34471981 ≤ 34603053) S016C06.total S016C07.total

theorem join_0_4 : (twinPrimeSegment 34603053 34865197).card = 1102 := by
  simpa using combineTwinPrimeSegments (by decide : 34603053 ≤ 34734125)
    (by decide : 34734125 ≤ 34865197) S016C08.total S016C09.total

theorem join_0_5 : (twinPrimeSegment 34865197 35127341).card = 1120 := by
  simpa using combineTwinPrimeSegments (by decide : 34865197 ≤ 34996269)
    (by decide : 34996269 ≤ 35127341) S016C10.total S016C11.total

theorem join_0_6 : (twinPrimeSegment 35127341 35389485).card = 1131 := by
  simpa using combineTwinPrimeSegments (by decide : 35127341 ≤ 35258413)
    (by decide : 35258413 ≤ 35389485) S016C12.total S016C13.total

theorem join_0_7 : (twinPrimeSegment 35389485 35651629).card = 1168 := by
  simpa using combineTwinPrimeSegments (by decide : 35389485 ≤ 35520557)
    (by decide : 35520557 ≤ 35651629) S016C14.total S016C15.total

theorem join_1_0 : (twinPrimeSegment 33554477 34078765).card = 2307 := by
  simpa using combineTwinPrimeSegments (by decide : 33554477 ≤ 33816621)
    (by decide : 33816621 ≤ 34078765) join_0_0 join_0_1

theorem join_1_1 : (twinPrimeSegment 34078765 34603053).card = 2289 := by
  simpa using combineTwinPrimeSegments (by decide : 34078765 ≤ 34340909)
    (by decide : 34340909 ≤ 34603053) join_0_2 join_0_3

theorem join_1_2 : (twinPrimeSegment 34603053 35127341).card = 2222 := by
  simpa using combineTwinPrimeSegments (by decide : 34603053 ≤ 34865197)
    (by decide : 34865197 ≤ 35127341) join_0_4 join_0_5

theorem join_1_3 : (twinPrimeSegment 35127341 35651629).card = 2299 := by
  simpa using combineTwinPrimeSegments (by decide : 35127341 ≤ 35389485)
    (by decide : 35389485 ≤ 35651629) join_0_6 join_0_7

theorem join_2_0 : (twinPrimeSegment 33554477 34603053).card = 4596 := by
  simpa using combineTwinPrimeSegments (by decide : 33554477 ≤ 34078765)
    (by decide : 34078765 ≤ 34603053) join_1_0 join_1_1

theorem join_2_1 : (twinPrimeSegment 34603053 35651629).card = 4521 := by
  simpa using combineTwinPrimeSegments (by decide : 34603053 ≤ 35127341)
    (by decide : 35127341 ≤ 35651629) join_1_2 join_1_3

theorem join_3_0 : (twinPrimeSegment 33554477 35651629).card = 9117 := by
  simpa using combineTwinPrimeSegments (by decide : 33554477 ≤ 34603053)
    (by decide : 34603053 ≤ 35651629) join_2_0 join_2_1

theorem total : (twinPrimeSegment 33554477 35651629).card = 9117 := join_3_0

end S016All
end Sude.GeneratedTwinScan
