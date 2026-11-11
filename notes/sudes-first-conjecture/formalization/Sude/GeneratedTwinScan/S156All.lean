import Sude.GeneratedTwinScan.S156C00
import Sude.GeneratedTwinScan.S156C01
import Sude.GeneratedTwinScan.S156C02
import Sude.GeneratedTwinScan.S156C03
import Sude.GeneratedTwinScan.S156C04
import Sude.GeneratedTwinScan.S156C05
import Sude.GeneratedTwinScan.S156C06
import Sude.GeneratedTwinScan.S156C07
import Sude.GeneratedTwinScan.S156C08
import Sude.GeneratedTwinScan.S156C09
import Sude.GeneratedTwinScan.S156C10
import Sude.GeneratedTwinScan.S156C11
import Sude.GeneratedTwinScan.S156C12
import Sude.GeneratedTwinScan.S156C13
import Sude.GeneratedTwinScan.S156C14
import Sude.GeneratedTwinScan.S156C15

/-! Combined FT source segment; Lean kernel check required. -/
namespace Sude.GeneratedTwinScan
namespace S156All

theorem join_0_0 : (twinPrimeSegment 327155757 327417901).card = 841 := by
  simpa using combineTwinPrimeSegments (by decide : 327155757 ≤ 327286829)
    (by decide : 327286829 ≤ 327417901) S156C00.total S156C01.total

theorem join_0_1 : (twinPrimeSegment 327417901 327680045).card = 908 := by
  simpa using combineTwinPrimeSegments (by decide : 327417901 ≤ 327548973)
    (by decide : 327548973 ≤ 327680045) S156C02.total S156C03.total

theorem join_0_2 : (twinPrimeSegment 327680045 327942189).card = 917 := by
  simpa using combineTwinPrimeSegments (by decide : 327680045 ≤ 327811117)
    (by decide : 327811117 ≤ 327942189) S156C04.total S156C05.total

theorem join_0_3 : (twinPrimeSegment 327942189 328204333).card = 880 := by
  simpa using combineTwinPrimeSegments (by decide : 327942189 ≤ 328073261)
    (by decide : 328073261 ≤ 328204333) S156C06.total S156C07.total

theorem join_0_4 : (twinPrimeSegment 328204333 328466477).card = 877 := by
  simpa using combineTwinPrimeSegments (by decide : 328204333 ≤ 328335405)
    (by decide : 328335405 ≤ 328466477) S156C08.total S156C09.total

theorem join_0_5 : (twinPrimeSegment 328466477 328728621).card = 875 := by
  simpa using combineTwinPrimeSegments (by decide : 328466477 ≤ 328597549)
    (by decide : 328597549 ≤ 328728621) S156C10.total S156C11.total

theorem join_0_6 : (twinPrimeSegment 328728621 328990765).card = 954 := by
  simpa using combineTwinPrimeSegments (by decide : 328728621 ≤ 328859693)
    (by decide : 328859693 ≤ 328990765) S156C12.total S156C13.total

theorem join_0_7 : (twinPrimeSegment 328990765 329252909).card = 891 := by
  simpa using combineTwinPrimeSegments (by decide : 328990765 ≤ 329121837)
    (by decide : 329121837 ≤ 329252909) S156C14.total S156C15.total

theorem join_1_0 : (twinPrimeSegment 327155757 327680045).card = 1749 := by
  simpa using combineTwinPrimeSegments (by decide : 327155757 ≤ 327417901)
    (by decide : 327417901 ≤ 327680045) join_0_0 join_0_1

theorem join_1_1 : (twinPrimeSegment 327680045 328204333).card = 1797 := by
  simpa using combineTwinPrimeSegments (by decide : 327680045 ≤ 327942189)
    (by decide : 327942189 ≤ 328204333) join_0_2 join_0_3

theorem join_1_2 : (twinPrimeSegment 328204333 328728621).card = 1752 := by
  simpa using combineTwinPrimeSegments (by decide : 328204333 ≤ 328466477)
    (by decide : 328466477 ≤ 328728621) join_0_4 join_0_5

theorem join_1_3 : (twinPrimeSegment 328728621 329252909).card = 1845 := by
  simpa using combineTwinPrimeSegments (by decide : 328728621 ≤ 328990765)
    (by decide : 328990765 ≤ 329252909) join_0_6 join_0_7

theorem join_2_0 : (twinPrimeSegment 327155757 328204333).card = 3546 := by
  simpa using combineTwinPrimeSegments (by decide : 327155757 ≤ 327680045)
    (by decide : 327680045 ≤ 328204333) join_1_0 join_1_1

theorem join_2_1 : (twinPrimeSegment 328204333 329252909).card = 3597 := by
  simpa using combineTwinPrimeSegments (by decide : 328204333 ≤ 328728621)
    (by decide : 328728621 ≤ 329252909) join_1_2 join_1_3

theorem join_3_0 : (twinPrimeSegment 327155757 329252909).card = 7143 := by
  simpa using combineTwinPrimeSegments (by decide : 327155757 ≤ 328204333)
    (by decide : 328204333 ≤ 329252909) join_2_0 join_2_1

theorem total : (twinPrimeSegment 327155757 329252909).card = 7143 := join_3_0

end S156All
end Sude.GeneratedTwinScan
