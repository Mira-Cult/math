import Sude.GeneratedTwinScan.S150C00
import Sude.GeneratedTwinScan.S150C01
import Sude.GeneratedTwinScan.S150C02
import Sude.GeneratedTwinScan.S150C03
import Sude.GeneratedTwinScan.S150C04
import Sude.GeneratedTwinScan.S150C05
import Sude.GeneratedTwinScan.S150C06
import Sude.GeneratedTwinScan.S150C07
import Sude.GeneratedTwinScan.S150C08
import Sude.GeneratedTwinScan.S150C09
import Sude.GeneratedTwinScan.S150C10
import Sude.GeneratedTwinScan.S150C11
import Sude.GeneratedTwinScan.S150C12
import Sude.GeneratedTwinScan.S150C13
import Sude.GeneratedTwinScan.S150C14
import Sude.GeneratedTwinScan.S150C15

/-! Combined FT source segment; Lean kernel check required. -/
namespace Sude.GeneratedTwinScan
namespace S150All

theorem join_0_0 : (twinPrimeSegment 314572845 314834989).card = 929 := by
  simpa using combineTwinPrimeSegments (by decide : 314572845 ≤ 314703917)
    (by decide : 314703917 ≤ 314834989) S150C00.total S150C01.total

theorem join_0_1 : (twinPrimeSegment 314834989 315097133).card = 875 := by
  simpa using combineTwinPrimeSegments (by decide : 314834989 ≤ 314966061)
    (by decide : 314966061 ≤ 315097133) S150C02.total S150C03.total

theorem join_0_2 : (twinPrimeSegment 315097133 315359277).card = 885 := by
  simpa using combineTwinPrimeSegments (by decide : 315097133 ≤ 315228205)
    (by decide : 315228205 ≤ 315359277) S150C04.total S150C05.total

theorem join_0_3 : (twinPrimeSegment 315359277 315621421).card = 904 := by
  simpa using combineTwinPrimeSegments (by decide : 315359277 ≤ 315490349)
    (by decide : 315490349 ≤ 315621421) S150C06.total S150C07.total

theorem join_0_4 : (twinPrimeSegment 315621421 315883565).card = 864 := by
  simpa using combineTwinPrimeSegments (by decide : 315621421 ≤ 315752493)
    (by decide : 315752493 ≤ 315883565) S150C08.total S150C09.total

theorem join_0_5 : (twinPrimeSegment 315883565 316145709).card = 862 := by
  simpa using combineTwinPrimeSegments (by decide : 315883565 ≤ 316014637)
    (by decide : 316014637 ≤ 316145709) S150C10.total S150C11.total

theorem join_0_6 : (twinPrimeSegment 316145709 316407853).card = 916 := by
  simpa using combineTwinPrimeSegments (by decide : 316145709 ≤ 316276781)
    (by decide : 316276781 ≤ 316407853) S150C12.total S150C13.total

theorem join_0_7 : (twinPrimeSegment 316407853 316669997).card = 905 := by
  simpa using combineTwinPrimeSegments (by decide : 316407853 ≤ 316538925)
    (by decide : 316538925 ≤ 316669997) S150C14.total S150C15.total

theorem join_1_0 : (twinPrimeSegment 314572845 315097133).card = 1804 := by
  simpa using combineTwinPrimeSegments (by decide : 314572845 ≤ 314834989)
    (by decide : 314834989 ≤ 315097133) join_0_0 join_0_1

theorem join_1_1 : (twinPrimeSegment 315097133 315621421).card = 1789 := by
  simpa using combineTwinPrimeSegments (by decide : 315097133 ≤ 315359277)
    (by decide : 315359277 ≤ 315621421) join_0_2 join_0_3

theorem join_1_2 : (twinPrimeSegment 315621421 316145709).card = 1726 := by
  simpa using combineTwinPrimeSegments (by decide : 315621421 ≤ 315883565)
    (by decide : 315883565 ≤ 316145709) join_0_4 join_0_5

theorem join_1_3 : (twinPrimeSegment 316145709 316669997).card = 1821 := by
  simpa using combineTwinPrimeSegments (by decide : 316145709 ≤ 316407853)
    (by decide : 316407853 ≤ 316669997) join_0_6 join_0_7

theorem join_2_0 : (twinPrimeSegment 314572845 315621421).card = 3593 := by
  simpa using combineTwinPrimeSegments (by decide : 314572845 ≤ 315097133)
    (by decide : 315097133 ≤ 315621421) join_1_0 join_1_1

theorem join_2_1 : (twinPrimeSegment 315621421 316669997).card = 3547 := by
  simpa using combineTwinPrimeSegments (by decide : 315621421 ≤ 316145709)
    (by decide : 316145709 ≤ 316669997) join_1_2 join_1_3

theorem join_3_0 : (twinPrimeSegment 314572845 316669997).card = 7140 := by
  simpa using combineTwinPrimeSegments (by decide : 314572845 ≤ 315621421)
    (by decide : 315621421 ≤ 316669997) join_2_0 join_2_1

theorem total : (twinPrimeSegment 314572845 316669997).card = 7140 := join_3_0

end S150All
end Sude.GeneratedTwinScan
