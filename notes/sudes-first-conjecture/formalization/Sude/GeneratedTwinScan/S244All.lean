import Sude.GeneratedTwinScan.S244C00
import Sude.GeneratedTwinScan.S244C01
import Sude.GeneratedTwinScan.S244C02
import Sude.GeneratedTwinScan.S244C03
import Sude.GeneratedTwinScan.S244C04
import Sude.GeneratedTwinScan.S244C05
import Sude.GeneratedTwinScan.S244C06
import Sude.GeneratedTwinScan.S244C07
import Sude.GeneratedTwinScan.S244C08
import Sude.GeneratedTwinScan.S244C09
import Sude.GeneratedTwinScan.S244C10
import Sude.GeneratedTwinScan.S244C11
import Sude.GeneratedTwinScan.S244C12
import Sude.GeneratedTwinScan.S244C13
import Sude.GeneratedTwinScan.S244C14
import Sude.GeneratedTwinScan.S244C15

/-! Combined FT source segment; Lean kernel check required. -/
namespace Sude.GeneratedTwinScan
namespace S244All

theorem join_0_0 : (twinPrimeSegment 511705133 511967277).card = 854 := by
  simpa using combineTwinPrimeSegments (by decide : 511705133 ≤ 511836205)
    (by decide : 511836205 ≤ 511967277) S244C00.total S244C01.total

theorem join_0_1 : (twinPrimeSegment 511967277 512229421).card = 870 := by
  simpa using combineTwinPrimeSegments (by decide : 511967277 ≤ 512098349)
    (by decide : 512098349 ≤ 512229421) S244C02.total S244C03.total

theorem join_0_2 : (twinPrimeSegment 512229421 512491565).card = 840 := by
  simpa using combineTwinPrimeSegments (by decide : 512229421 ≤ 512360493)
    (by decide : 512360493 ≤ 512491565) S244C04.total S244C05.total

theorem join_0_3 : (twinPrimeSegment 512491565 512753709).card = 857 := by
  simpa using combineTwinPrimeSegments (by decide : 512491565 ≤ 512622637)
    (by decide : 512622637 ≤ 512753709) S244C06.total S244C07.total

theorem join_0_4 : (twinPrimeSegment 512753709 513015853).card = 845 := by
  simpa using combineTwinPrimeSegments (by decide : 512753709 ≤ 512884781)
    (by decide : 512884781 ≤ 513015853) S244C08.total S244C09.total

theorem join_0_5 : (twinPrimeSegment 513015853 513277997).card = 882 := by
  simpa using combineTwinPrimeSegments (by decide : 513015853 ≤ 513146925)
    (by decide : 513146925 ≤ 513277997) S244C10.total S244C11.total

theorem join_0_6 : (twinPrimeSegment 513277997 513540141).card = 915 := by
  simpa using combineTwinPrimeSegments (by decide : 513277997 ≤ 513409069)
    (by decide : 513409069 ≤ 513540141) S244C12.total S244C13.total

theorem join_0_7 : (twinPrimeSegment 513540141 513802285).card = 819 := by
  simpa using combineTwinPrimeSegments (by decide : 513540141 ≤ 513671213)
    (by decide : 513671213 ≤ 513802285) S244C14.total S244C15.total

theorem join_1_0 : (twinPrimeSegment 511705133 512229421).card = 1724 := by
  simpa using combineTwinPrimeSegments (by decide : 511705133 ≤ 511967277)
    (by decide : 511967277 ≤ 512229421) join_0_0 join_0_1

theorem join_1_1 : (twinPrimeSegment 512229421 512753709).card = 1697 := by
  simpa using combineTwinPrimeSegments (by decide : 512229421 ≤ 512491565)
    (by decide : 512491565 ≤ 512753709) join_0_2 join_0_3

theorem join_1_2 : (twinPrimeSegment 512753709 513277997).card = 1727 := by
  simpa using combineTwinPrimeSegments (by decide : 512753709 ≤ 513015853)
    (by decide : 513015853 ≤ 513277997) join_0_4 join_0_5

theorem join_1_3 : (twinPrimeSegment 513277997 513802285).card = 1734 := by
  simpa using combineTwinPrimeSegments (by decide : 513277997 ≤ 513540141)
    (by decide : 513540141 ≤ 513802285) join_0_6 join_0_7

theorem join_2_0 : (twinPrimeSegment 511705133 512753709).card = 3421 := by
  simpa using combineTwinPrimeSegments (by decide : 511705133 ≤ 512229421)
    (by decide : 512229421 ≤ 512753709) join_1_0 join_1_1

theorem join_2_1 : (twinPrimeSegment 512753709 513802285).card = 3461 := by
  simpa using combineTwinPrimeSegments (by decide : 512753709 ≤ 513277997)
    (by decide : 513277997 ≤ 513802285) join_1_2 join_1_3

theorem join_3_0 : (twinPrimeSegment 511705133 513802285).card = 6882 := by
  simpa using combineTwinPrimeSegments (by decide : 511705133 ≤ 512753709)
    (by decide : 512753709 ≤ 513802285) join_2_0 join_2_1

theorem total : (twinPrimeSegment 511705133 513802285).card = 6882 := join_3_0

end S244All
end Sude.GeneratedTwinScan
