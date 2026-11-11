import Sude.GeneratedTwinScan.S243C00
import Sude.GeneratedTwinScan.S243C01
import Sude.GeneratedTwinScan.S243C02
import Sude.GeneratedTwinScan.S243C03
import Sude.GeneratedTwinScan.S243C04
import Sude.GeneratedTwinScan.S243C05
import Sude.GeneratedTwinScan.S243C06
import Sude.GeneratedTwinScan.S243C07
import Sude.GeneratedTwinScan.S243C08
import Sude.GeneratedTwinScan.S243C09
import Sude.GeneratedTwinScan.S243C10
import Sude.GeneratedTwinScan.S243C11
import Sude.GeneratedTwinScan.S243C12
import Sude.GeneratedTwinScan.S243C13
import Sude.GeneratedTwinScan.S243C14
import Sude.GeneratedTwinScan.S243C15

/-! Combined FT source segment; Lean kernel check required. -/
namespace Sude.GeneratedTwinScan
namespace S243All

theorem join_0_0 : (twinPrimeSegment 509607981 509870125).card = 814 := by
  simpa using combineTwinPrimeSegments (by decide : 509607981 ≤ 509739053)
    (by decide : 509739053 ≤ 509870125) S243C00.total S243C01.total

theorem join_0_1 : (twinPrimeSegment 509870125 510132269).card = 860 := by
  simpa using combineTwinPrimeSegments (by decide : 509870125 ≤ 510001197)
    (by decide : 510001197 ≤ 510132269) S243C02.total S243C03.total

theorem join_0_2 : (twinPrimeSegment 510132269 510394413).card = 875 := by
  simpa using combineTwinPrimeSegments (by decide : 510132269 ≤ 510263341)
    (by decide : 510263341 ≤ 510394413) S243C04.total S243C05.total

theorem join_0_3 : (twinPrimeSegment 510394413 510656557).card = 873 := by
  simpa using combineTwinPrimeSegments (by decide : 510394413 ≤ 510525485)
    (by decide : 510525485 ≤ 510656557) S243C06.total S243C07.total

theorem join_0_4 : (twinPrimeSegment 510656557 510918701).card = 784 := by
  simpa using combineTwinPrimeSegments (by decide : 510656557 ≤ 510787629)
    (by decide : 510787629 ≤ 510918701) S243C08.total S243C09.total

theorem join_0_5 : (twinPrimeSegment 510918701 511180845).card = 863 := by
  simpa using combineTwinPrimeSegments (by decide : 510918701 ≤ 511049773)
    (by decide : 511049773 ≤ 511180845) S243C10.total S243C11.total

theorem join_0_6 : (twinPrimeSegment 511180845 511442989).card = 871 := by
  simpa using combineTwinPrimeSegments (by decide : 511180845 ≤ 511311917)
    (by decide : 511311917 ≤ 511442989) S243C12.total S243C13.total

theorem join_0_7 : (twinPrimeSegment 511442989 511705133).card = 849 := by
  simpa using combineTwinPrimeSegments (by decide : 511442989 ≤ 511574061)
    (by decide : 511574061 ≤ 511705133) S243C14.total S243C15.total

theorem join_1_0 : (twinPrimeSegment 509607981 510132269).card = 1674 := by
  simpa using combineTwinPrimeSegments (by decide : 509607981 ≤ 509870125)
    (by decide : 509870125 ≤ 510132269) join_0_0 join_0_1

theorem join_1_1 : (twinPrimeSegment 510132269 510656557).card = 1748 := by
  simpa using combineTwinPrimeSegments (by decide : 510132269 ≤ 510394413)
    (by decide : 510394413 ≤ 510656557) join_0_2 join_0_3

theorem join_1_2 : (twinPrimeSegment 510656557 511180845).card = 1647 := by
  simpa using combineTwinPrimeSegments (by decide : 510656557 ≤ 510918701)
    (by decide : 510918701 ≤ 511180845) join_0_4 join_0_5

theorem join_1_3 : (twinPrimeSegment 511180845 511705133).card = 1720 := by
  simpa using combineTwinPrimeSegments (by decide : 511180845 ≤ 511442989)
    (by decide : 511442989 ≤ 511705133) join_0_6 join_0_7

theorem join_2_0 : (twinPrimeSegment 509607981 510656557).card = 3422 := by
  simpa using combineTwinPrimeSegments (by decide : 509607981 ≤ 510132269)
    (by decide : 510132269 ≤ 510656557) join_1_0 join_1_1

theorem join_2_1 : (twinPrimeSegment 510656557 511705133).card = 3367 := by
  simpa using combineTwinPrimeSegments (by decide : 510656557 ≤ 511180845)
    (by decide : 511180845 ≤ 511705133) join_1_2 join_1_3

theorem join_3_0 : (twinPrimeSegment 509607981 511705133).card = 6789 := by
  simpa using combineTwinPrimeSegments (by decide : 509607981 ≤ 510656557)
    (by decide : 510656557 ≤ 511705133) join_2_0 join_2_1

theorem total : (twinPrimeSegment 509607981 511705133).card = 6789 := join_3_0

end S243All
end Sude.GeneratedTwinScan
