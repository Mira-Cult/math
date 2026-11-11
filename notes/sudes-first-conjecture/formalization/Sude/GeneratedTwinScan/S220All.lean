import Sude.GeneratedTwinScan.S220C00
import Sude.GeneratedTwinScan.S220C01
import Sude.GeneratedTwinScan.S220C02
import Sude.GeneratedTwinScan.S220C03
import Sude.GeneratedTwinScan.S220C04
import Sude.GeneratedTwinScan.S220C05
import Sude.GeneratedTwinScan.S220C06
import Sude.GeneratedTwinScan.S220C07
import Sude.GeneratedTwinScan.S220C08
import Sude.GeneratedTwinScan.S220C09
import Sude.GeneratedTwinScan.S220C10
import Sude.GeneratedTwinScan.S220C11
import Sude.GeneratedTwinScan.S220C12
import Sude.GeneratedTwinScan.S220C13
import Sude.GeneratedTwinScan.S220C14
import Sude.GeneratedTwinScan.S220C15

/-! Combined FT source segment; Lean kernel check required. -/
namespace Sude.GeneratedTwinScan
namespace S220All

theorem join_0_0 : (twinPrimeSegment 461373485 461635629).card = 864 := by
  simpa using combineTwinPrimeSegments (by decide : 461373485 ≤ 461504557)
    (by decide : 461504557 ≤ 461635629) S220C00.total S220C01.total

theorem join_0_1 : (twinPrimeSegment 461635629 461897773).card = 868 := by
  simpa using combineTwinPrimeSegments (by decide : 461635629 ≤ 461766701)
    (by decide : 461766701 ≤ 461897773) S220C02.total S220C03.total

theorem join_0_2 : (twinPrimeSegment 461897773 462159917).card = 873 := by
  simpa using combineTwinPrimeSegments (by decide : 461897773 ≤ 462028845)
    (by decide : 462028845 ≤ 462159917) S220C04.total S220C05.total

theorem join_0_3 : (twinPrimeSegment 462159917 462422061).card = 863 := by
  simpa using combineTwinPrimeSegments (by decide : 462159917 ≤ 462290989)
    (by decide : 462290989 ≤ 462422061) S220C06.total S220C07.total

theorem join_0_4 : (twinPrimeSegment 462422061 462684205).card = 874 := by
  simpa using combineTwinPrimeSegments (by decide : 462422061 ≤ 462553133)
    (by decide : 462553133 ≤ 462684205) S220C08.total S220C09.total

theorem join_0_5 : (twinPrimeSegment 462684205 462946349).card = 863 := by
  simpa using combineTwinPrimeSegments (by decide : 462684205 ≤ 462815277)
    (by decide : 462815277 ≤ 462946349) S220C10.total S220C11.total

theorem join_0_6 : (twinPrimeSegment 462946349 463208493).card = 832 := by
  simpa using combineTwinPrimeSegments (by decide : 462946349 ≤ 463077421)
    (by decide : 463077421 ≤ 463208493) S220C12.total S220C13.total

theorem join_0_7 : (twinPrimeSegment 463208493 463470637).card = 867 := by
  simpa using combineTwinPrimeSegments (by decide : 463208493 ≤ 463339565)
    (by decide : 463339565 ≤ 463470637) S220C14.total S220C15.total

theorem join_1_0 : (twinPrimeSegment 461373485 461897773).card = 1732 := by
  simpa using combineTwinPrimeSegments (by decide : 461373485 ≤ 461635629)
    (by decide : 461635629 ≤ 461897773) join_0_0 join_0_1

theorem join_1_1 : (twinPrimeSegment 461897773 462422061).card = 1736 := by
  simpa using combineTwinPrimeSegments (by decide : 461897773 ≤ 462159917)
    (by decide : 462159917 ≤ 462422061) join_0_2 join_0_3

theorem join_1_2 : (twinPrimeSegment 462422061 462946349).card = 1737 := by
  simpa using combineTwinPrimeSegments (by decide : 462422061 ≤ 462684205)
    (by decide : 462684205 ≤ 462946349) join_0_4 join_0_5

theorem join_1_3 : (twinPrimeSegment 462946349 463470637).card = 1699 := by
  simpa using combineTwinPrimeSegments (by decide : 462946349 ≤ 463208493)
    (by decide : 463208493 ≤ 463470637) join_0_6 join_0_7

theorem join_2_0 : (twinPrimeSegment 461373485 462422061).card = 3468 := by
  simpa using combineTwinPrimeSegments (by decide : 461373485 ≤ 461897773)
    (by decide : 461897773 ≤ 462422061) join_1_0 join_1_1

theorem join_2_1 : (twinPrimeSegment 462422061 463470637).card = 3436 := by
  simpa using combineTwinPrimeSegments (by decide : 462422061 ≤ 462946349)
    (by decide : 462946349 ≤ 463470637) join_1_2 join_1_3

theorem join_3_0 : (twinPrimeSegment 461373485 463470637).card = 6904 := by
  simpa using combineTwinPrimeSegments (by decide : 461373485 ≤ 462422061)
    (by decide : 462422061 ≤ 463470637) join_2_0 join_2_1

theorem total : (twinPrimeSegment 461373485 463470637).card = 6904 := join_3_0

end S220All
end Sude.GeneratedTwinScan
