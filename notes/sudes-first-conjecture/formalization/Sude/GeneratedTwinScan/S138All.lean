import Sude.GeneratedTwinScan.S138C00
import Sude.GeneratedTwinScan.S138C01
import Sude.GeneratedTwinScan.S138C02
import Sude.GeneratedTwinScan.S138C03
import Sude.GeneratedTwinScan.S138C04
import Sude.GeneratedTwinScan.S138C05
import Sude.GeneratedTwinScan.S138C06
import Sude.GeneratedTwinScan.S138C07
import Sude.GeneratedTwinScan.S138C08
import Sude.GeneratedTwinScan.S138C09
import Sude.GeneratedTwinScan.S138C10
import Sude.GeneratedTwinScan.S138C11
import Sude.GeneratedTwinScan.S138C12
import Sude.GeneratedTwinScan.S138C13
import Sude.GeneratedTwinScan.S138C14
import Sude.GeneratedTwinScan.S138C15

/-! Combined FT source segment; Lean kernel check required. -/
namespace Sude.GeneratedTwinScan
namespace S138All

theorem join_0_0 : (twinPrimeSegment 289407021 289669165).card = 939 := by
  simpa using combineTwinPrimeSegments (by decide : 289407021 ≤ 289538093)
    (by decide : 289538093 ≤ 289669165) S138C00.total S138C01.total

theorem join_0_1 : (twinPrimeSegment 289669165 289931309).card = 916 := by
  simpa using combineTwinPrimeSegments (by decide : 289669165 ≤ 289800237)
    (by decide : 289800237 ≤ 289931309) S138C02.total S138C03.total

theorem join_0_2 : (twinPrimeSegment 289931309 290193453).card = 905 := by
  simpa using combineTwinPrimeSegments (by decide : 289931309 ≤ 290062381)
    (by decide : 290062381 ≤ 290193453) S138C04.total S138C05.total

theorem join_0_3 : (twinPrimeSegment 290193453 290455597).card = 925 := by
  simpa using combineTwinPrimeSegments (by decide : 290193453 ≤ 290324525)
    (by decide : 290324525 ≤ 290455597) S138C06.total S138C07.total

theorem join_0_4 : (twinPrimeSegment 290455597 290717741).card = 918 := by
  simpa using combineTwinPrimeSegments (by decide : 290455597 ≤ 290586669)
    (by decide : 290586669 ≤ 290717741) S138C08.total S138C09.total

theorem join_0_5 : (twinPrimeSegment 290717741 290979885).card = 916 := by
  simpa using combineTwinPrimeSegments (by decide : 290717741 ≤ 290848813)
    (by decide : 290848813 ≤ 290979885) S138C10.total S138C11.total

theorem join_0_6 : (twinPrimeSegment 290979885 291242029).card = 890 := by
  simpa using combineTwinPrimeSegments (by decide : 290979885 ≤ 291110957)
    (by decide : 291110957 ≤ 291242029) S138C12.total S138C13.total

theorem join_0_7 : (twinPrimeSegment 291242029 291504173).card = 897 := by
  simpa using combineTwinPrimeSegments (by decide : 291242029 ≤ 291373101)
    (by decide : 291373101 ≤ 291504173) S138C14.total S138C15.total

theorem join_1_0 : (twinPrimeSegment 289407021 289931309).card = 1855 := by
  simpa using combineTwinPrimeSegments (by decide : 289407021 ≤ 289669165)
    (by decide : 289669165 ≤ 289931309) join_0_0 join_0_1

theorem join_1_1 : (twinPrimeSegment 289931309 290455597).card = 1830 := by
  simpa using combineTwinPrimeSegments (by decide : 289931309 ≤ 290193453)
    (by decide : 290193453 ≤ 290455597) join_0_2 join_0_3

theorem join_1_2 : (twinPrimeSegment 290455597 290979885).card = 1834 := by
  simpa using combineTwinPrimeSegments (by decide : 290455597 ≤ 290717741)
    (by decide : 290717741 ≤ 290979885) join_0_4 join_0_5

theorem join_1_3 : (twinPrimeSegment 290979885 291504173).card = 1787 := by
  simpa using combineTwinPrimeSegments (by decide : 290979885 ≤ 291242029)
    (by decide : 291242029 ≤ 291504173) join_0_6 join_0_7

theorem join_2_0 : (twinPrimeSegment 289407021 290455597).card = 3685 := by
  simpa using combineTwinPrimeSegments (by decide : 289407021 ≤ 289931309)
    (by decide : 289931309 ≤ 290455597) join_1_0 join_1_1

theorem join_2_1 : (twinPrimeSegment 290455597 291504173).card = 3621 := by
  simpa using combineTwinPrimeSegments (by decide : 290455597 ≤ 290979885)
    (by decide : 290979885 ≤ 291504173) join_1_2 join_1_3

theorem join_3_0 : (twinPrimeSegment 289407021 291504173).card = 7306 := by
  simpa using combineTwinPrimeSegments (by decide : 289407021 ≤ 290455597)
    (by decide : 290455597 ≤ 291504173) join_2_0 join_2_1

theorem total : (twinPrimeSegment 289407021 291504173).card = 7306 := join_3_0

end S138All
end Sude.GeneratedTwinScan
