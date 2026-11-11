import Sude.GeneratedTwinScan.S236C00
import Sude.GeneratedTwinScan.S236C01
import Sude.GeneratedTwinScan.S236C02
import Sude.GeneratedTwinScan.S236C03
import Sude.GeneratedTwinScan.S236C04
import Sude.GeneratedTwinScan.S236C05
import Sude.GeneratedTwinScan.S236C06
import Sude.GeneratedTwinScan.S236C07
import Sude.GeneratedTwinScan.S236C08
import Sude.GeneratedTwinScan.S236C09
import Sude.GeneratedTwinScan.S236C10
import Sude.GeneratedTwinScan.S236C11
import Sude.GeneratedTwinScan.S236C12
import Sude.GeneratedTwinScan.S236C13
import Sude.GeneratedTwinScan.S236C14
import Sude.GeneratedTwinScan.S236C15

/-! Combined FT source segment; Lean kernel check required. -/
namespace Sude.GeneratedTwinScan
namespace S236All

theorem join_0_0 : (twinPrimeSegment 494927917 495190061).card = 870 := by
  simpa using combineTwinPrimeSegments (by decide : 494927917 ≤ 495058989)
    (by decide : 495058989 ≤ 495190061) S236C00.total S236C01.total

theorem join_0_1 : (twinPrimeSegment 495190061 495452205).card = 877 := by
  simpa using combineTwinPrimeSegments (by decide : 495190061 ≤ 495321133)
    (by decide : 495321133 ≤ 495452205) S236C02.total S236C03.total

theorem join_0_2 : (twinPrimeSegment 495452205 495714349).card = 851 := by
  simpa using combineTwinPrimeSegments (by decide : 495452205 ≤ 495583277)
    (by decide : 495583277 ≤ 495714349) S236C04.total S236C05.total

theorem join_0_3 : (twinPrimeSegment 495714349 495976493).card = 850 := by
  simpa using combineTwinPrimeSegments (by decide : 495714349 ≤ 495845421)
    (by decide : 495845421 ≤ 495976493) S236C06.total S236C07.total

theorem join_0_4 : (twinPrimeSegment 495976493 496238637).card = 885 := by
  simpa using combineTwinPrimeSegments (by decide : 495976493 ≤ 496107565)
    (by decide : 496107565 ≤ 496238637) S236C08.total S236C09.total

theorem join_0_5 : (twinPrimeSegment 496238637 496500781).card = 865 := by
  simpa using combineTwinPrimeSegments (by decide : 496238637 ≤ 496369709)
    (by decide : 496369709 ≤ 496500781) S236C10.total S236C11.total

theorem join_0_6 : (twinPrimeSegment 496500781 496762925).card = 862 := by
  simpa using combineTwinPrimeSegments (by decide : 496500781 ≤ 496631853)
    (by decide : 496631853 ≤ 496762925) S236C12.total S236C13.total

theorem join_0_7 : (twinPrimeSegment 496762925 497025069).card = 842 := by
  simpa using combineTwinPrimeSegments (by decide : 496762925 ≤ 496893997)
    (by decide : 496893997 ≤ 497025069) S236C14.total S236C15.total

theorem join_1_0 : (twinPrimeSegment 494927917 495452205).card = 1747 := by
  simpa using combineTwinPrimeSegments (by decide : 494927917 ≤ 495190061)
    (by decide : 495190061 ≤ 495452205) join_0_0 join_0_1

theorem join_1_1 : (twinPrimeSegment 495452205 495976493).card = 1701 := by
  simpa using combineTwinPrimeSegments (by decide : 495452205 ≤ 495714349)
    (by decide : 495714349 ≤ 495976493) join_0_2 join_0_3

theorem join_1_2 : (twinPrimeSegment 495976493 496500781).card = 1750 := by
  simpa using combineTwinPrimeSegments (by decide : 495976493 ≤ 496238637)
    (by decide : 496238637 ≤ 496500781) join_0_4 join_0_5

theorem join_1_3 : (twinPrimeSegment 496500781 497025069).card = 1704 := by
  simpa using combineTwinPrimeSegments (by decide : 496500781 ≤ 496762925)
    (by decide : 496762925 ≤ 497025069) join_0_6 join_0_7

theorem join_2_0 : (twinPrimeSegment 494927917 495976493).card = 3448 := by
  simpa using combineTwinPrimeSegments (by decide : 494927917 ≤ 495452205)
    (by decide : 495452205 ≤ 495976493) join_1_0 join_1_1

theorem join_2_1 : (twinPrimeSegment 495976493 497025069).card = 3454 := by
  simpa using combineTwinPrimeSegments (by decide : 495976493 ≤ 496500781)
    (by decide : 496500781 ≤ 497025069) join_1_2 join_1_3

theorem join_3_0 : (twinPrimeSegment 494927917 497025069).card = 6902 := by
  simpa using combineTwinPrimeSegments (by decide : 494927917 ≤ 495976493)
    (by decide : 495976493 ≤ 497025069) join_2_0 join_2_1

theorem total : (twinPrimeSegment 494927917 497025069).card = 6902 := join_3_0

end S236All
end Sude.GeneratedTwinScan
