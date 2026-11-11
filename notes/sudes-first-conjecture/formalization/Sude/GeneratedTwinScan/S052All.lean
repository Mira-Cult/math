import Sude.GeneratedTwinScan.S052C00
import Sude.GeneratedTwinScan.S052C01
import Sude.GeneratedTwinScan.S052C02
import Sude.GeneratedTwinScan.S052C03
import Sude.GeneratedTwinScan.S052C04
import Sude.GeneratedTwinScan.S052C05
import Sude.GeneratedTwinScan.S052C06
import Sude.GeneratedTwinScan.S052C07
import Sude.GeneratedTwinScan.S052C08
import Sude.GeneratedTwinScan.S052C09
import Sude.GeneratedTwinScan.S052C10
import Sude.GeneratedTwinScan.S052C11
import Sude.GeneratedTwinScan.S052C12
import Sude.GeneratedTwinScan.S052C13
import Sude.GeneratedTwinScan.S052C14
import Sude.GeneratedTwinScan.S052C15

/-! Combined FT source segment; Lean kernel check required. -/
namespace Sude.GeneratedTwinScan
namespace S052All

theorem join_0_0 : (twinPrimeSegment 109051949 109314093).card = 970 := by
  simpa using combineTwinPrimeSegments (by decide : 109051949 ≤ 109183021)
    (by decide : 109183021 ≤ 109314093) S052C00.total S052C01.total

theorem join_0_1 : (twinPrimeSegment 109314093 109576237).card = 1031 := by
  simpa using combineTwinPrimeSegments (by decide : 109314093 ≤ 109445165)
    (by decide : 109445165 ≤ 109576237) S052C02.total S052C03.total

theorem join_0_2 : (twinPrimeSegment 109576237 109838381).card = 1004 := by
  simpa using combineTwinPrimeSegments (by decide : 109576237 ≤ 109707309)
    (by decide : 109707309 ≤ 109838381) S052C04.total S052C05.total

theorem join_0_3 : (twinPrimeSegment 109838381 110100525).card = 1025 := by
  simpa using combineTwinPrimeSegments (by decide : 109838381 ≤ 109969453)
    (by decide : 109969453 ≤ 110100525) S052C06.total S052C07.total

theorem join_0_4 : (twinPrimeSegment 110100525 110362669).card = 1016 := by
  simpa using combineTwinPrimeSegments (by decide : 110100525 ≤ 110231597)
    (by decide : 110231597 ≤ 110362669) S052C08.total S052C09.total

theorem join_0_5 : (twinPrimeSegment 110362669 110624813).card = 1048 := by
  simpa using combineTwinPrimeSegments (by decide : 110362669 ≤ 110493741)
    (by decide : 110493741 ≤ 110624813) S052C10.total S052C11.total

theorem join_0_6 : (twinPrimeSegment 110624813 110886957).card = 1012 := by
  simpa using combineTwinPrimeSegments (by decide : 110624813 ≤ 110755885)
    (by decide : 110755885 ≤ 110886957) S052C12.total S052C13.total

theorem join_0_7 : (twinPrimeSegment 110886957 111149101).card = 1015 := by
  simpa using combineTwinPrimeSegments (by decide : 110886957 ≤ 111018029)
    (by decide : 111018029 ≤ 111149101) S052C14.total S052C15.total

theorem join_1_0 : (twinPrimeSegment 109051949 109576237).card = 2001 := by
  simpa using combineTwinPrimeSegments (by decide : 109051949 ≤ 109314093)
    (by decide : 109314093 ≤ 109576237) join_0_0 join_0_1

theorem join_1_1 : (twinPrimeSegment 109576237 110100525).card = 2029 := by
  simpa using combineTwinPrimeSegments (by decide : 109576237 ≤ 109838381)
    (by decide : 109838381 ≤ 110100525) join_0_2 join_0_3

theorem join_1_2 : (twinPrimeSegment 110100525 110624813).card = 2064 := by
  simpa using combineTwinPrimeSegments (by decide : 110100525 ≤ 110362669)
    (by decide : 110362669 ≤ 110624813) join_0_4 join_0_5

theorem join_1_3 : (twinPrimeSegment 110624813 111149101).card = 2027 := by
  simpa using combineTwinPrimeSegments (by decide : 110624813 ≤ 110886957)
    (by decide : 110886957 ≤ 111149101) join_0_6 join_0_7

theorem join_2_0 : (twinPrimeSegment 109051949 110100525).card = 4030 := by
  simpa using combineTwinPrimeSegments (by decide : 109051949 ≤ 109576237)
    (by decide : 109576237 ≤ 110100525) join_1_0 join_1_1

theorem join_2_1 : (twinPrimeSegment 110100525 111149101).card = 4091 := by
  simpa using combineTwinPrimeSegments (by decide : 110100525 ≤ 110624813)
    (by decide : 110624813 ≤ 111149101) join_1_2 join_1_3

theorem join_3_0 : (twinPrimeSegment 109051949 111149101).card = 8121 := by
  simpa using combineTwinPrimeSegments (by decide : 109051949 ≤ 110100525)
    (by decide : 110100525 ≤ 111149101) join_2_0 join_2_1

theorem total : (twinPrimeSegment 109051949 111149101).card = 8121 := join_3_0

end S052All
end Sude.GeneratedTwinScan
