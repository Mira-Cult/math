import Sude.GeneratedTwinScan.S013C00
import Sude.GeneratedTwinScan.S013C01
import Sude.GeneratedTwinScan.S013C02
import Sude.GeneratedTwinScan.S013C03
import Sude.GeneratedTwinScan.S013C04
import Sude.GeneratedTwinScan.S013C05
import Sude.GeneratedTwinScan.S013C06
import Sude.GeneratedTwinScan.S013C07
import Sude.GeneratedTwinScan.S013C08
import Sude.GeneratedTwinScan.S013C09
import Sude.GeneratedTwinScan.S013C10
import Sude.GeneratedTwinScan.S013C11
import Sude.GeneratedTwinScan.S013C12
import Sude.GeneratedTwinScan.S013C13
import Sude.GeneratedTwinScan.S013C14
import Sude.GeneratedTwinScan.S013C15

/-! Combined FT source segment; Lean kernel check required. -/
namespace Sude.GeneratedTwinScan
namespace S013All

theorem join_0_0 : (twinPrimeSegment 27263021 27525165).card = 1111 := by
  simpa using combineTwinPrimeSegments (by decide : 27263021 ≤ 27394093)
    (by decide : 27394093 ≤ 27525165) S013C00.total S013C01.total

theorem join_0_1 : (twinPrimeSegment 27525165 27787309).card = 1162 := by
  simpa using combineTwinPrimeSegments (by decide : 27525165 ≤ 27656237)
    (by decide : 27656237 ≤ 27787309) S013C02.total S013C03.total

theorem join_0_2 : (twinPrimeSegment 27787309 28049453).card = 1215 := by
  simpa using combineTwinPrimeSegments (by decide : 27787309 ≤ 27918381)
    (by decide : 27918381 ≤ 28049453) S013C04.total S013C05.total

theorem join_0_3 : (twinPrimeSegment 28049453 28311597).card = 1110 := by
  simpa using combineTwinPrimeSegments (by decide : 28049453 ≤ 28180525)
    (by decide : 28180525 ≤ 28311597) S013C06.total S013C07.total

theorem join_0_4 : (twinPrimeSegment 28311597 28573741).card = 1236 := by
  simpa using combineTwinPrimeSegments (by decide : 28311597 ≤ 28442669)
    (by decide : 28442669 ≤ 28573741) S013C08.total S013C09.total

theorem join_0_5 : (twinPrimeSegment 28573741 28835885).card = 1149 := by
  simpa using combineTwinPrimeSegments (by decide : 28573741 ≤ 28704813)
    (by decide : 28704813 ≤ 28835885) S013C10.total S013C11.total

theorem join_0_6 : (twinPrimeSegment 28835885 29098029).card = 1194 := by
  simpa using combineTwinPrimeSegments (by decide : 28835885 ≤ 28966957)
    (by decide : 28966957 ≤ 29098029) S013C12.total S013C13.total

theorem join_0_7 : (twinPrimeSegment 29098029 29360173).card = 1165 := by
  simpa using combineTwinPrimeSegments (by decide : 29098029 ≤ 29229101)
    (by decide : 29229101 ≤ 29360173) S013C14.total S013C15.total

theorem join_1_0 : (twinPrimeSegment 27263021 27787309).card = 2273 := by
  simpa using combineTwinPrimeSegments (by decide : 27263021 ≤ 27525165)
    (by decide : 27525165 ≤ 27787309) join_0_0 join_0_1

theorem join_1_1 : (twinPrimeSegment 27787309 28311597).card = 2325 := by
  simpa using combineTwinPrimeSegments (by decide : 27787309 ≤ 28049453)
    (by decide : 28049453 ≤ 28311597) join_0_2 join_0_3

theorem join_1_2 : (twinPrimeSegment 28311597 28835885).card = 2385 := by
  simpa using combineTwinPrimeSegments (by decide : 28311597 ≤ 28573741)
    (by decide : 28573741 ≤ 28835885) join_0_4 join_0_5

theorem join_1_3 : (twinPrimeSegment 28835885 29360173).card = 2359 := by
  simpa using combineTwinPrimeSegments (by decide : 28835885 ≤ 29098029)
    (by decide : 29098029 ≤ 29360173) join_0_6 join_0_7

theorem join_2_0 : (twinPrimeSegment 27263021 28311597).card = 4598 := by
  simpa using combineTwinPrimeSegments (by decide : 27263021 ≤ 27787309)
    (by decide : 27787309 ≤ 28311597) join_1_0 join_1_1

theorem join_2_1 : (twinPrimeSegment 28311597 29360173).card = 4744 := by
  simpa using combineTwinPrimeSegments (by decide : 28311597 ≤ 28835885)
    (by decide : 28835885 ≤ 29360173) join_1_2 join_1_3

theorem join_3_0 : (twinPrimeSegment 27263021 29360173).card = 9342 := by
  simpa using combineTwinPrimeSegments (by decide : 27263021 ≤ 28311597)
    (by decide : 28311597 ≤ 29360173) join_2_0 join_2_1

theorem total : (twinPrimeSegment 27263021 29360173).card = 9342 := join_3_0

end S013All
end Sude.GeneratedTwinScan
