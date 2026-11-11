import Sude.GeneratedTwinScan.S086C00
import Sude.GeneratedTwinScan.S086C01
import Sude.GeneratedTwinScan.S086C02
import Sude.GeneratedTwinScan.S086C03
import Sude.GeneratedTwinScan.S086C04
import Sude.GeneratedTwinScan.S086C05
import Sude.GeneratedTwinScan.S086C06
import Sude.GeneratedTwinScan.S086C07
import Sude.GeneratedTwinScan.S086C08
import Sude.GeneratedTwinScan.S086C09
import Sude.GeneratedTwinScan.S086C10
import Sude.GeneratedTwinScan.S086C11
import Sude.GeneratedTwinScan.S086C12
import Sude.GeneratedTwinScan.S086C13
import Sude.GeneratedTwinScan.S086C14
import Sude.GeneratedTwinScan.S086C15

/-! Combined FT source segment; Lean kernel check required. -/
namespace Sude.GeneratedTwinScan
namespace S086All

theorem join_0_0 : (twinPrimeSegment 180355117 180617261).card = 923 := by
  simpa using combineTwinPrimeSegments (by decide : 180355117 ≤ 180486189)
    (by decide : 180486189 ≤ 180617261) S086C00.total S086C01.total

theorem join_0_1 : (twinPrimeSegment 180617261 180879405).card = 949 := by
  simpa using combineTwinPrimeSegments (by decide : 180617261 ≤ 180748333)
    (by decide : 180748333 ≤ 180879405) S086C02.total S086C03.total

theorem join_0_2 : (twinPrimeSegment 180879405 181141549).card = 928 := by
  simpa using combineTwinPrimeSegments (by decide : 180879405 ≤ 181010477)
    (by decide : 181010477 ≤ 181141549) S086C04.total S086C05.total

theorem join_0_3 : (twinPrimeSegment 181141549 181403693).card = 955 := by
  simpa using combineTwinPrimeSegments (by decide : 181141549 ≤ 181272621)
    (by decide : 181272621 ≤ 181403693) S086C06.total S086C07.total

theorem join_0_4 : (twinPrimeSegment 181403693 181665837).card = 965 := by
  simpa using combineTwinPrimeSegments (by decide : 181403693 ≤ 181534765)
    (by decide : 181534765 ≤ 181665837) S086C08.total S086C09.total

theorem join_0_5 : (twinPrimeSegment 181665837 181927981).card = 940 := by
  simpa using combineTwinPrimeSegments (by decide : 181665837 ≤ 181796909)
    (by decide : 181796909 ≤ 181927981) S086C10.total S086C11.total

theorem join_0_6 : (twinPrimeSegment 181927981 182190125).card = 944 := by
  simpa using combineTwinPrimeSegments (by decide : 181927981 ≤ 182059053)
    (by decide : 182059053 ≤ 182190125) S086C12.total S086C13.total

theorem join_0_7 : (twinPrimeSegment 182190125 182452269).card = 938 := by
  simpa using combineTwinPrimeSegments (by decide : 182190125 ≤ 182321197)
    (by decide : 182321197 ≤ 182452269) S086C14.total S086C15.total

theorem join_1_0 : (twinPrimeSegment 180355117 180879405).card = 1872 := by
  simpa using combineTwinPrimeSegments (by decide : 180355117 ≤ 180617261)
    (by decide : 180617261 ≤ 180879405) join_0_0 join_0_1

theorem join_1_1 : (twinPrimeSegment 180879405 181403693).card = 1883 := by
  simpa using combineTwinPrimeSegments (by decide : 180879405 ≤ 181141549)
    (by decide : 181141549 ≤ 181403693) join_0_2 join_0_3

theorem join_1_2 : (twinPrimeSegment 181403693 181927981).card = 1905 := by
  simpa using combineTwinPrimeSegments (by decide : 181403693 ≤ 181665837)
    (by decide : 181665837 ≤ 181927981) join_0_4 join_0_5

theorem join_1_3 : (twinPrimeSegment 181927981 182452269).card = 1882 := by
  simpa using combineTwinPrimeSegments (by decide : 181927981 ≤ 182190125)
    (by decide : 182190125 ≤ 182452269) join_0_6 join_0_7

theorem join_2_0 : (twinPrimeSegment 180355117 181403693).card = 3755 := by
  simpa using combineTwinPrimeSegments (by decide : 180355117 ≤ 180879405)
    (by decide : 180879405 ≤ 181403693) join_1_0 join_1_1

theorem join_2_1 : (twinPrimeSegment 181403693 182452269).card = 3787 := by
  simpa using combineTwinPrimeSegments (by decide : 181403693 ≤ 181927981)
    (by decide : 181927981 ≤ 182452269) join_1_2 join_1_3

theorem join_3_0 : (twinPrimeSegment 180355117 182452269).card = 7542 := by
  simpa using combineTwinPrimeSegments (by decide : 180355117 ≤ 181403693)
    (by decide : 181403693 ≤ 182452269) join_2_0 join_2_1

theorem total : (twinPrimeSegment 180355117 182452269).card = 7542 := join_3_0

end S086All
end Sude.GeneratedTwinScan
