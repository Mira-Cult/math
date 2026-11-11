import Sude.GeneratedTwinScan.S060C00
import Sude.GeneratedTwinScan.S060C01
import Sude.GeneratedTwinScan.S060C02
import Sude.GeneratedTwinScan.S060C03
import Sude.GeneratedTwinScan.S060C04
import Sude.GeneratedTwinScan.S060C05
import Sude.GeneratedTwinScan.S060C06
import Sude.GeneratedTwinScan.S060C07
import Sude.GeneratedTwinScan.S060C08
import Sude.GeneratedTwinScan.S060C09
import Sude.GeneratedTwinScan.S060C10
import Sude.GeneratedTwinScan.S060C11
import Sude.GeneratedTwinScan.S060C12
import Sude.GeneratedTwinScan.S060C13
import Sude.GeneratedTwinScan.S060C14
import Sude.GeneratedTwinScan.S060C15

/-! Combined FT source segment; Lean kernel check required. -/
namespace Sude.GeneratedTwinScan
namespace S060All

theorem join_0_0 : (twinPrimeSegment 125829165 126091309).card = 972 := by
  simpa using combineTwinPrimeSegments (by decide : 125829165 ≤ 125960237)
    (by decide : 125960237 ≤ 126091309) S060C00.total S060C01.total

theorem join_0_1 : (twinPrimeSegment 126091309 126353453).card = 1015 := by
  simpa using combineTwinPrimeSegments (by decide : 126091309 ≤ 126222381)
    (by decide : 126222381 ≤ 126353453) S060C02.total S060C03.total

theorem join_0_2 : (twinPrimeSegment 126353453 126615597).card = 969 := by
  simpa using combineTwinPrimeSegments (by decide : 126353453 ≤ 126484525)
    (by decide : 126484525 ≤ 126615597) S060C04.total S060C05.total

theorem join_0_3 : (twinPrimeSegment 126615597 126877741).card = 994 := by
  simpa using combineTwinPrimeSegments (by decide : 126615597 ≤ 126746669)
    (by decide : 126746669 ≤ 126877741) S060C06.total S060C07.total

theorem join_0_4 : (twinPrimeSegment 126877741 127139885).card = 1026 := by
  simpa using combineTwinPrimeSegments (by decide : 126877741 ≤ 127008813)
    (by decide : 127008813 ≤ 127139885) S060C08.total S060C09.total

theorem join_0_5 : (twinPrimeSegment 127139885 127402029).card = 969 := by
  simpa using combineTwinPrimeSegments (by decide : 127139885 ≤ 127270957)
    (by decide : 127270957 ≤ 127402029) S060C10.total S060C11.total

theorem join_0_6 : (twinPrimeSegment 127402029 127664173).card = 1001 := by
  simpa using combineTwinPrimeSegments (by decide : 127402029 ≤ 127533101)
    (by decide : 127533101 ≤ 127664173) S060C12.total S060C13.total

theorem join_0_7 : (twinPrimeSegment 127664173 127926317).card = 1002 := by
  simpa using combineTwinPrimeSegments (by decide : 127664173 ≤ 127795245)
    (by decide : 127795245 ≤ 127926317) S060C14.total S060C15.total

theorem join_1_0 : (twinPrimeSegment 125829165 126353453).card = 1987 := by
  simpa using combineTwinPrimeSegments (by decide : 125829165 ≤ 126091309)
    (by decide : 126091309 ≤ 126353453) join_0_0 join_0_1

theorem join_1_1 : (twinPrimeSegment 126353453 126877741).card = 1963 := by
  simpa using combineTwinPrimeSegments (by decide : 126353453 ≤ 126615597)
    (by decide : 126615597 ≤ 126877741) join_0_2 join_0_3

theorem join_1_2 : (twinPrimeSegment 126877741 127402029).card = 1995 := by
  simpa using combineTwinPrimeSegments (by decide : 126877741 ≤ 127139885)
    (by decide : 127139885 ≤ 127402029) join_0_4 join_0_5

theorem join_1_3 : (twinPrimeSegment 127402029 127926317).card = 2003 := by
  simpa using combineTwinPrimeSegments (by decide : 127402029 ≤ 127664173)
    (by decide : 127664173 ≤ 127926317) join_0_6 join_0_7

theorem join_2_0 : (twinPrimeSegment 125829165 126877741).card = 3950 := by
  simpa using combineTwinPrimeSegments (by decide : 125829165 ≤ 126353453)
    (by decide : 126353453 ≤ 126877741) join_1_0 join_1_1

theorem join_2_1 : (twinPrimeSegment 126877741 127926317).card = 3998 := by
  simpa using combineTwinPrimeSegments (by decide : 126877741 ≤ 127402029)
    (by decide : 127402029 ≤ 127926317) join_1_2 join_1_3

theorem join_3_0 : (twinPrimeSegment 125829165 127926317).card = 7948 := by
  simpa using combineTwinPrimeSegments (by decide : 125829165 ≤ 126877741)
    (by decide : 126877741 ≤ 127926317) join_2_0 join_2_1

theorem total : (twinPrimeSegment 125829165 127926317).card = 7948 := join_3_0

end S060All
end Sude.GeneratedTwinScan
