import Sude.GeneratedTwinScan.S196C00
import Sude.GeneratedTwinScan.S196C01
import Sude.GeneratedTwinScan.S196C02
import Sude.GeneratedTwinScan.S196C03
import Sude.GeneratedTwinScan.S196C04
import Sude.GeneratedTwinScan.S196C05
import Sude.GeneratedTwinScan.S196C06
import Sude.GeneratedTwinScan.S196C07
import Sude.GeneratedTwinScan.S196C08
import Sude.GeneratedTwinScan.S196C09
import Sude.GeneratedTwinScan.S196C10
import Sude.GeneratedTwinScan.S196C11
import Sude.GeneratedTwinScan.S196C12
import Sude.GeneratedTwinScan.S196C13
import Sude.GeneratedTwinScan.S196C14
import Sude.GeneratedTwinScan.S196C15

/-! Combined FT source segment; Lean kernel check required. -/
namespace Sude.GeneratedTwinScan
namespace S196All

theorem join_0_0 : (twinPrimeSegment 411041837 411303981).card = 864 := by
  simpa using combineTwinPrimeSegments (by decide : 411041837 ≤ 411172909)
    (by decide : 411172909 ≤ 411303981) S196C00.total S196C01.total

theorem join_0_1 : (twinPrimeSegment 411303981 411566125).card = 894 := by
  simpa using combineTwinPrimeSegments (by decide : 411303981 ≤ 411435053)
    (by decide : 411435053 ≤ 411566125) S196C02.total S196C03.total

theorem join_0_2 : (twinPrimeSegment 411566125 411828269).card = 831 := by
  simpa using combineTwinPrimeSegments (by decide : 411566125 ≤ 411697197)
    (by decide : 411697197 ≤ 411828269) S196C04.total S196C05.total

theorem join_0_3 : (twinPrimeSegment 411828269 412090413).card = 918 := by
  simpa using combineTwinPrimeSegments (by decide : 411828269 ≤ 411959341)
    (by decide : 411959341 ≤ 412090413) S196C06.total S196C07.total

theorem join_0_4 : (twinPrimeSegment 412090413 412352557).card = 885 := by
  simpa using combineTwinPrimeSegments (by decide : 412090413 ≤ 412221485)
    (by decide : 412221485 ≤ 412352557) S196C08.total S196C09.total

theorem join_0_5 : (twinPrimeSegment 412352557 412614701).card = 871 := by
  simpa using combineTwinPrimeSegments (by decide : 412352557 ≤ 412483629)
    (by decide : 412483629 ≤ 412614701) S196C10.total S196C11.total

theorem join_0_6 : (twinPrimeSegment 412614701 412876845).card = 885 := by
  simpa using combineTwinPrimeSegments (by decide : 412614701 ≤ 412745773)
    (by decide : 412745773 ≤ 412876845) S196C12.total S196C13.total

theorem join_0_7 : (twinPrimeSegment 412876845 413138989).card = 875 := by
  simpa using combineTwinPrimeSegments (by decide : 412876845 ≤ 413007917)
    (by decide : 413007917 ≤ 413138989) S196C14.total S196C15.total

theorem join_1_0 : (twinPrimeSegment 411041837 411566125).card = 1758 := by
  simpa using combineTwinPrimeSegments (by decide : 411041837 ≤ 411303981)
    (by decide : 411303981 ≤ 411566125) join_0_0 join_0_1

theorem join_1_1 : (twinPrimeSegment 411566125 412090413).card = 1749 := by
  simpa using combineTwinPrimeSegments (by decide : 411566125 ≤ 411828269)
    (by decide : 411828269 ≤ 412090413) join_0_2 join_0_3

theorem join_1_2 : (twinPrimeSegment 412090413 412614701).card = 1756 := by
  simpa using combineTwinPrimeSegments (by decide : 412090413 ≤ 412352557)
    (by decide : 412352557 ≤ 412614701) join_0_4 join_0_5

theorem join_1_3 : (twinPrimeSegment 412614701 413138989).card = 1760 := by
  simpa using combineTwinPrimeSegments (by decide : 412614701 ≤ 412876845)
    (by decide : 412876845 ≤ 413138989) join_0_6 join_0_7

theorem join_2_0 : (twinPrimeSegment 411041837 412090413).card = 3507 := by
  simpa using combineTwinPrimeSegments (by decide : 411041837 ≤ 411566125)
    (by decide : 411566125 ≤ 412090413) join_1_0 join_1_1

theorem join_2_1 : (twinPrimeSegment 412090413 413138989).card = 3516 := by
  simpa using combineTwinPrimeSegments (by decide : 412090413 ≤ 412614701)
    (by decide : 412614701 ≤ 413138989) join_1_2 join_1_3

theorem join_3_0 : (twinPrimeSegment 411041837 413138989).card = 7023 := by
  simpa using combineTwinPrimeSegments (by decide : 411041837 ≤ 412090413)
    (by decide : 412090413 ≤ 413138989) join_2_0 join_2_1

theorem total : (twinPrimeSegment 411041837 413138989).card = 7023 := join_3_0

end S196All
end Sude.GeneratedTwinScan
