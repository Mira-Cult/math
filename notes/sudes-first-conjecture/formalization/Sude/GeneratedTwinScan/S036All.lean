import Sude.GeneratedTwinScan.S036C00
import Sude.GeneratedTwinScan.S036C01
import Sude.GeneratedTwinScan.S036C02
import Sude.GeneratedTwinScan.S036C03
import Sude.GeneratedTwinScan.S036C04
import Sude.GeneratedTwinScan.S036C05
import Sude.GeneratedTwinScan.S036C06
import Sude.GeneratedTwinScan.S036C07
import Sude.GeneratedTwinScan.S036C08
import Sude.GeneratedTwinScan.S036C09
import Sude.GeneratedTwinScan.S036C10
import Sude.GeneratedTwinScan.S036C11
import Sude.GeneratedTwinScan.S036C12
import Sude.GeneratedTwinScan.S036C13
import Sude.GeneratedTwinScan.S036C14
import Sude.GeneratedTwinScan.S036C15

/-! Combined FT source segment; Lean kernel check required. -/
namespace Sude.GeneratedTwinScan
namespace S036All

theorem join_0_0 : (twinPrimeSegment 75497517 75759661).card = 1093 := by
  simpa using combineTwinPrimeSegments (by decide : 75497517 ≤ 75628589)
    (by decide : 75628589 ≤ 75759661) S036C00.total S036C01.total

theorem join_0_1 : (twinPrimeSegment 75759661 76021805).card = 1054 := by
  simpa using combineTwinPrimeSegments (by decide : 75759661 ≤ 75890733)
    (by decide : 75890733 ≤ 76021805) S036C02.total S036C03.total

theorem join_0_2 : (twinPrimeSegment 76021805 76283949).card = 1058 := by
  simpa using combineTwinPrimeSegments (by decide : 76021805 ≤ 76152877)
    (by decide : 76152877 ≤ 76283949) S036C04.total S036C05.total

theorem join_0_3 : (twinPrimeSegment 76283949 76546093).card = 1018 := by
  simpa using combineTwinPrimeSegments (by decide : 76283949 ≤ 76415021)
    (by decide : 76415021 ≤ 76546093) S036C06.total S036C07.total

theorem join_0_4 : (twinPrimeSegment 76546093 76808237).card = 1024 := by
  simpa using combineTwinPrimeSegments (by decide : 76546093 ≤ 76677165)
    (by decide : 76677165 ≤ 76808237) S036C08.total S036C09.total

theorem join_0_5 : (twinPrimeSegment 76808237 77070381).card = 1096 := by
  simpa using combineTwinPrimeSegments (by decide : 76808237 ≤ 76939309)
    (by decide : 76939309 ≤ 77070381) S036C10.total S036C11.total

theorem join_0_6 : (twinPrimeSegment 77070381 77332525).card = 1035 := by
  simpa using combineTwinPrimeSegments (by decide : 77070381 ≤ 77201453)
    (by decide : 77201453 ≤ 77332525) S036C12.total S036C13.total

theorem join_0_7 : (twinPrimeSegment 77332525 77594669).card = 1055 := by
  simpa using combineTwinPrimeSegments (by decide : 77332525 ≤ 77463597)
    (by decide : 77463597 ≤ 77594669) S036C14.total S036C15.total

theorem join_1_0 : (twinPrimeSegment 75497517 76021805).card = 2147 := by
  simpa using combineTwinPrimeSegments (by decide : 75497517 ≤ 75759661)
    (by decide : 75759661 ≤ 76021805) join_0_0 join_0_1

theorem join_1_1 : (twinPrimeSegment 76021805 76546093).card = 2076 := by
  simpa using combineTwinPrimeSegments (by decide : 76021805 ≤ 76283949)
    (by decide : 76283949 ≤ 76546093) join_0_2 join_0_3

theorem join_1_2 : (twinPrimeSegment 76546093 77070381).card = 2120 := by
  simpa using combineTwinPrimeSegments (by decide : 76546093 ≤ 76808237)
    (by decide : 76808237 ≤ 77070381) join_0_4 join_0_5

theorem join_1_3 : (twinPrimeSegment 77070381 77594669).card = 2090 := by
  simpa using combineTwinPrimeSegments (by decide : 77070381 ≤ 77332525)
    (by decide : 77332525 ≤ 77594669) join_0_6 join_0_7

theorem join_2_0 : (twinPrimeSegment 75497517 76546093).card = 4223 := by
  simpa using combineTwinPrimeSegments (by decide : 75497517 ≤ 76021805)
    (by decide : 76021805 ≤ 76546093) join_1_0 join_1_1

theorem join_2_1 : (twinPrimeSegment 76546093 77594669).card = 4210 := by
  simpa using combineTwinPrimeSegments (by decide : 76546093 ≤ 77070381)
    (by decide : 77070381 ≤ 77594669) join_1_2 join_1_3

theorem join_3_0 : (twinPrimeSegment 75497517 77594669).card = 8433 := by
  simpa using combineTwinPrimeSegments (by decide : 75497517 ≤ 76546093)
    (by decide : 76546093 ≤ 77594669) join_2_0 join_2_1

theorem total : (twinPrimeSegment 75497517 77594669).card = 8433 := join_3_0

end S036All
end Sude.GeneratedTwinScan
