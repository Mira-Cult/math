import Sude.GeneratedTwinScan.S044C00
import Sude.GeneratedTwinScan.S044C01
import Sude.GeneratedTwinScan.S044C02
import Sude.GeneratedTwinScan.S044C03
import Sude.GeneratedTwinScan.S044C04
import Sude.GeneratedTwinScan.S044C05
import Sude.GeneratedTwinScan.S044C06
import Sude.GeneratedTwinScan.S044C07
import Sude.GeneratedTwinScan.S044C08
import Sude.GeneratedTwinScan.S044C09
import Sude.GeneratedTwinScan.S044C10
import Sude.GeneratedTwinScan.S044C11
import Sude.GeneratedTwinScan.S044C12
import Sude.GeneratedTwinScan.S044C13
import Sude.GeneratedTwinScan.S044C14
import Sude.GeneratedTwinScan.S044C15

/-! Combined FT source segment; Lean kernel check required. -/
namespace Sude.GeneratedTwinScan
namespace S044All

theorem join_0_0 : (twinPrimeSegment 92274733 92536877).card = 969 := by
  simpa using combineTwinPrimeSegments (by decide : 92274733 ≤ 92405805)
    (by decide : 92405805 ≤ 92536877) S044C00.total S044C01.total

theorem join_0_1 : (twinPrimeSegment 92536877 92799021).card = 1048 := by
  simpa using combineTwinPrimeSegments (by decide : 92536877 ≤ 92667949)
    (by decide : 92667949 ≤ 92799021) S044C02.total S044C03.total

theorem join_0_2 : (twinPrimeSegment 92799021 93061165).card = 1042 := by
  simpa using combineTwinPrimeSegments (by decide : 92799021 ≤ 92930093)
    (by decide : 92930093 ≤ 93061165) S044C04.total S044C05.total

theorem join_0_3 : (twinPrimeSegment 93061165 93323309).card = 1021 := by
  simpa using combineTwinPrimeSegments (by decide : 93061165 ≤ 93192237)
    (by decide : 93192237 ≤ 93323309) S044C06.total S044C07.total

theorem join_0_4 : (twinPrimeSegment 93323309 93585453).card = 1047 := by
  simpa using combineTwinPrimeSegments (by decide : 93323309 ≤ 93454381)
    (by decide : 93454381 ≤ 93585453) S044C08.total S044C09.total

theorem join_0_5 : (twinPrimeSegment 93585453 93847597).card = 983 := by
  simpa using combineTwinPrimeSegments (by decide : 93585453 ≤ 93716525)
    (by decide : 93716525 ≤ 93847597) S044C10.total S044C11.total

theorem join_0_6 : (twinPrimeSegment 93847597 94109741).card = 1041 := by
  simpa using combineTwinPrimeSegments (by decide : 93847597 ≤ 93978669)
    (by decide : 93978669 ≤ 94109741) S044C12.total S044C13.total

theorem join_0_7 : (twinPrimeSegment 94109741 94371885).card = 1029 := by
  simpa using combineTwinPrimeSegments (by decide : 94109741 ≤ 94240813)
    (by decide : 94240813 ≤ 94371885) S044C14.total S044C15.total

theorem join_1_0 : (twinPrimeSegment 92274733 92799021).card = 2017 := by
  simpa using combineTwinPrimeSegments (by decide : 92274733 ≤ 92536877)
    (by decide : 92536877 ≤ 92799021) join_0_0 join_0_1

theorem join_1_1 : (twinPrimeSegment 92799021 93323309).card = 2063 := by
  simpa using combineTwinPrimeSegments (by decide : 92799021 ≤ 93061165)
    (by decide : 93061165 ≤ 93323309) join_0_2 join_0_3

theorem join_1_2 : (twinPrimeSegment 93323309 93847597).card = 2030 := by
  simpa using combineTwinPrimeSegments (by decide : 93323309 ≤ 93585453)
    (by decide : 93585453 ≤ 93847597) join_0_4 join_0_5

theorem join_1_3 : (twinPrimeSegment 93847597 94371885).card = 2070 := by
  simpa using combineTwinPrimeSegments (by decide : 93847597 ≤ 94109741)
    (by decide : 94109741 ≤ 94371885) join_0_6 join_0_7

theorem join_2_0 : (twinPrimeSegment 92274733 93323309).card = 4080 := by
  simpa using combineTwinPrimeSegments (by decide : 92274733 ≤ 92799021)
    (by decide : 92799021 ≤ 93323309) join_1_0 join_1_1

theorem join_2_1 : (twinPrimeSegment 93323309 94371885).card = 4100 := by
  simpa using combineTwinPrimeSegments (by decide : 93323309 ≤ 93847597)
    (by decide : 93847597 ≤ 94371885) join_1_2 join_1_3

theorem join_3_0 : (twinPrimeSegment 92274733 94371885).card = 8180 := by
  simpa using combineTwinPrimeSegments (by decide : 92274733 ≤ 93323309)
    (by decide : 93323309 ≤ 94371885) join_2_0 join_2_1

theorem total : (twinPrimeSegment 92274733 94371885).card = 8180 := join_3_0

end S044All
end Sude.GeneratedTwinScan
