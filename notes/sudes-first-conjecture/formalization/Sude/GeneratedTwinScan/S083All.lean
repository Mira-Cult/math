import Sude.GeneratedTwinScan.S083C00
import Sude.GeneratedTwinScan.S083C01
import Sude.GeneratedTwinScan.S083C02
import Sude.GeneratedTwinScan.S083C03
import Sude.GeneratedTwinScan.S083C04
import Sude.GeneratedTwinScan.S083C05
import Sude.GeneratedTwinScan.S083C06
import Sude.GeneratedTwinScan.S083C07
import Sude.GeneratedTwinScan.S083C08
import Sude.GeneratedTwinScan.S083C09
import Sude.GeneratedTwinScan.S083C10
import Sude.GeneratedTwinScan.S083C11
import Sude.GeneratedTwinScan.S083C12
import Sude.GeneratedTwinScan.S083C13
import Sude.GeneratedTwinScan.S083C14
import Sude.GeneratedTwinScan.S083C15

/-! Combined FT source segment; Lean kernel check required. -/
namespace Sude.GeneratedTwinScan
namespace S083All

theorem join_0_0 : (twinPrimeSegment 174063661 174325805).card = 999 := by
  simpa using combineTwinPrimeSegments (by decide : 174063661 ≤ 174194733)
    (by decide : 174194733 ≤ 174325805) S083C00.total S083C01.total

theorem join_0_1 : (twinPrimeSegment 174325805 174587949).card = 944 := by
  simpa using combineTwinPrimeSegments (by decide : 174325805 ≤ 174456877)
    (by decide : 174456877 ≤ 174587949) S083C02.total S083C03.total

theorem join_0_2 : (twinPrimeSegment 174587949 174850093).card = 920 := by
  simpa using combineTwinPrimeSegments (by decide : 174587949 ≤ 174719021)
    (by decide : 174719021 ≤ 174850093) S083C04.total S083C05.total

theorem join_0_3 : (twinPrimeSegment 174850093 175112237).card = 975 := by
  simpa using combineTwinPrimeSegments (by decide : 174850093 ≤ 174981165)
    (by decide : 174981165 ≤ 175112237) S083C06.total S083C07.total

theorem join_0_4 : (twinPrimeSegment 175112237 175374381).card = 984 := by
  simpa using combineTwinPrimeSegments (by decide : 175112237 ≤ 175243309)
    (by decide : 175243309 ≤ 175374381) S083C08.total S083C09.total

theorem join_0_5 : (twinPrimeSegment 175374381 175636525).card = 931 := by
  simpa using combineTwinPrimeSegments (by decide : 175374381 ≤ 175505453)
    (by decide : 175505453 ≤ 175636525) S083C10.total S083C11.total

theorem join_0_6 : (twinPrimeSegment 175636525 175898669).card = 978 := by
  simpa using combineTwinPrimeSegments (by decide : 175636525 ≤ 175767597)
    (by decide : 175767597 ≤ 175898669) S083C12.total S083C13.total

theorem join_0_7 : (twinPrimeSegment 175898669 176160813).card = 1009 := by
  simpa using combineTwinPrimeSegments (by decide : 175898669 ≤ 176029741)
    (by decide : 176029741 ≤ 176160813) S083C14.total S083C15.total

theorem join_1_0 : (twinPrimeSegment 174063661 174587949).card = 1943 := by
  simpa using combineTwinPrimeSegments (by decide : 174063661 ≤ 174325805)
    (by decide : 174325805 ≤ 174587949) join_0_0 join_0_1

theorem join_1_1 : (twinPrimeSegment 174587949 175112237).card = 1895 := by
  simpa using combineTwinPrimeSegments (by decide : 174587949 ≤ 174850093)
    (by decide : 174850093 ≤ 175112237) join_0_2 join_0_3

theorem join_1_2 : (twinPrimeSegment 175112237 175636525).card = 1915 := by
  simpa using combineTwinPrimeSegments (by decide : 175112237 ≤ 175374381)
    (by decide : 175374381 ≤ 175636525) join_0_4 join_0_5

theorem join_1_3 : (twinPrimeSegment 175636525 176160813).card = 1987 := by
  simpa using combineTwinPrimeSegments (by decide : 175636525 ≤ 175898669)
    (by decide : 175898669 ≤ 176160813) join_0_6 join_0_7

theorem join_2_0 : (twinPrimeSegment 174063661 175112237).card = 3838 := by
  simpa using combineTwinPrimeSegments (by decide : 174063661 ≤ 174587949)
    (by decide : 174587949 ≤ 175112237) join_1_0 join_1_1

theorem join_2_1 : (twinPrimeSegment 175112237 176160813).card = 3902 := by
  simpa using combineTwinPrimeSegments (by decide : 175112237 ≤ 175636525)
    (by decide : 175636525 ≤ 176160813) join_1_2 join_1_3

theorem join_3_0 : (twinPrimeSegment 174063661 176160813).card = 7740 := by
  simpa using combineTwinPrimeSegments (by decide : 174063661 ≤ 175112237)
    (by decide : 175112237 ≤ 176160813) join_2_0 join_2_1

theorem total : (twinPrimeSegment 174063661 176160813).card = 7740 := join_3_0

end S083All
end Sude.GeneratedTwinScan
