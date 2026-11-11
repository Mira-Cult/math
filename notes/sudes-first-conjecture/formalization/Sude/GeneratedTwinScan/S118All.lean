import Sude.GeneratedTwinScan.S118C00
import Sude.GeneratedTwinScan.S118C01
import Sude.GeneratedTwinScan.S118C02
import Sude.GeneratedTwinScan.S118C03
import Sude.GeneratedTwinScan.S118C04
import Sude.GeneratedTwinScan.S118C05
import Sude.GeneratedTwinScan.S118C06
import Sude.GeneratedTwinScan.S118C07
import Sude.GeneratedTwinScan.S118C08
import Sude.GeneratedTwinScan.S118C09
import Sude.GeneratedTwinScan.S118C10
import Sude.GeneratedTwinScan.S118C11
import Sude.GeneratedTwinScan.S118C12
import Sude.GeneratedTwinScan.S118C13
import Sude.GeneratedTwinScan.S118C14
import Sude.GeneratedTwinScan.S118C15

/-! Combined FT source segment; Lean kernel check required. -/
namespace Sude.GeneratedTwinScan
namespace S118All

theorem join_0_0 : (twinPrimeSegment 247463981 247726125).card = 887 := by
  simpa using combineTwinPrimeSegments (by decide : 247463981 ≤ 247595053)
    (by decide : 247595053 ≤ 247726125) S118C00.total S118C01.total

theorem join_0_1 : (twinPrimeSegment 247726125 247988269).card = 977 := by
  simpa using combineTwinPrimeSegments (by decide : 247726125 ≤ 247857197)
    (by decide : 247857197 ≤ 247988269) S118C02.total S118C03.total

theorem join_0_2 : (twinPrimeSegment 247988269 248250413).card = 910 := by
  simpa using combineTwinPrimeSegments (by decide : 247988269 ≤ 248119341)
    (by decide : 248119341 ≤ 248250413) S118C04.total S118C05.total

theorem join_0_3 : (twinPrimeSegment 248250413 248512557).card = 912 := by
  simpa using combineTwinPrimeSegments (by decide : 248250413 ≤ 248381485)
    (by decide : 248381485 ≤ 248512557) S118C06.total S118C07.total

theorem join_0_4 : (twinPrimeSegment 248512557 248774701).card = 903 := by
  simpa using combineTwinPrimeSegments (by decide : 248512557 ≤ 248643629)
    (by decide : 248643629 ≤ 248774701) S118C08.total S118C09.total

theorem join_0_5 : (twinPrimeSegment 248774701 249036845).card = 898 := by
  simpa using combineTwinPrimeSegments (by decide : 248774701 ≤ 248905773)
    (by decide : 248905773 ≤ 249036845) S118C10.total S118C11.total

theorem join_0_6 : (twinPrimeSegment 249036845 249298989).card = 940 := by
  simpa using combineTwinPrimeSegments (by decide : 249036845 ≤ 249167917)
    (by decide : 249167917 ≤ 249298989) S118C12.total S118C13.total

theorem join_0_7 : (twinPrimeSegment 249298989 249561133).card = 938 := by
  simpa using combineTwinPrimeSegments (by decide : 249298989 ≤ 249430061)
    (by decide : 249430061 ≤ 249561133) S118C14.total S118C15.total

theorem join_1_0 : (twinPrimeSegment 247463981 247988269).card = 1864 := by
  simpa using combineTwinPrimeSegments (by decide : 247463981 ≤ 247726125)
    (by decide : 247726125 ≤ 247988269) join_0_0 join_0_1

theorem join_1_1 : (twinPrimeSegment 247988269 248512557).card = 1822 := by
  simpa using combineTwinPrimeSegments (by decide : 247988269 ≤ 248250413)
    (by decide : 248250413 ≤ 248512557) join_0_2 join_0_3

theorem join_1_2 : (twinPrimeSegment 248512557 249036845).card = 1801 := by
  simpa using combineTwinPrimeSegments (by decide : 248512557 ≤ 248774701)
    (by decide : 248774701 ≤ 249036845) join_0_4 join_0_5

theorem join_1_3 : (twinPrimeSegment 249036845 249561133).card = 1878 := by
  simpa using combineTwinPrimeSegments (by decide : 249036845 ≤ 249298989)
    (by decide : 249298989 ≤ 249561133) join_0_6 join_0_7

theorem join_2_0 : (twinPrimeSegment 247463981 248512557).card = 3686 := by
  simpa using combineTwinPrimeSegments (by decide : 247463981 ≤ 247988269)
    (by decide : 247988269 ≤ 248512557) join_1_0 join_1_1

theorem join_2_1 : (twinPrimeSegment 248512557 249561133).card = 3679 := by
  simpa using combineTwinPrimeSegments (by decide : 248512557 ≤ 249036845)
    (by decide : 249036845 ≤ 249561133) join_1_2 join_1_3

theorem join_3_0 : (twinPrimeSegment 247463981 249561133).card = 7365 := by
  simpa using combineTwinPrimeSegments (by decide : 247463981 ≤ 248512557)
    (by decide : 248512557 ≤ 249561133) join_2_0 join_2_1

theorem total : (twinPrimeSegment 247463981 249561133).card = 7365 := join_3_0

end S118All
end Sude.GeneratedTwinScan
