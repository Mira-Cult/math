import Sude.GeneratedTwinScan.S061C00
import Sude.GeneratedTwinScan.S061C01
import Sude.GeneratedTwinScan.S061C02
import Sude.GeneratedTwinScan.S061C03
import Sude.GeneratedTwinScan.S061C04
import Sude.GeneratedTwinScan.S061C05
import Sude.GeneratedTwinScan.S061C06
import Sude.GeneratedTwinScan.S061C07
import Sude.GeneratedTwinScan.S061C08
import Sude.GeneratedTwinScan.S061C09
import Sude.GeneratedTwinScan.S061C10
import Sude.GeneratedTwinScan.S061C11
import Sude.GeneratedTwinScan.S061C12
import Sude.GeneratedTwinScan.S061C13
import Sude.GeneratedTwinScan.S061C14
import Sude.GeneratedTwinScan.S061C15

/-! Combined FT source segment; Lean kernel check required. -/
namespace Sude.GeneratedTwinScan
namespace S061All

theorem join_0_0 : (twinPrimeSegment 127926317 128188461).card = 977 := by
  simpa using combineTwinPrimeSegments (by decide : 127926317 ≤ 128057389)
    (by decide : 128057389 ≤ 128188461) S061C00.total S061C01.total

theorem join_0_1 : (twinPrimeSegment 128188461 128450605).card = 1010 := by
  simpa using combineTwinPrimeSegments (by decide : 128188461 ≤ 128319533)
    (by decide : 128319533 ≤ 128450605) S061C02.total S061C03.total

theorem join_0_2 : (twinPrimeSegment 128450605 128712749).card = 1001 := by
  simpa using combineTwinPrimeSegments (by decide : 128450605 ≤ 128581677)
    (by decide : 128581677 ≤ 128712749) S061C04.total S061C05.total

theorem join_0_3 : (twinPrimeSegment 128712749 128974893).card = 1026 := by
  simpa using combineTwinPrimeSegments (by decide : 128712749 ≤ 128843821)
    (by decide : 128843821 ≤ 128974893) S061C06.total S061C07.total

theorem join_0_4 : (twinPrimeSegment 128974893 129237037).card = 980 := by
  simpa using combineTwinPrimeSegments (by decide : 128974893 ≤ 129105965)
    (by decide : 129105965 ≤ 129237037) S061C08.total S061C09.total

theorem join_0_5 : (twinPrimeSegment 129237037 129499181).card = 1021 := by
  simpa using combineTwinPrimeSegments (by decide : 129237037 ≤ 129368109)
    (by decide : 129368109 ≤ 129499181) S061C10.total S061C11.total

theorem join_0_6 : (twinPrimeSegment 129499181 129761325).card = 1053 := by
  simpa using combineTwinPrimeSegments (by decide : 129499181 ≤ 129630253)
    (by decide : 129630253 ≤ 129761325) S061C12.total S061C13.total

theorem join_0_7 : (twinPrimeSegment 129761325 130023469).card = 958 := by
  simpa using combineTwinPrimeSegments (by decide : 129761325 ≤ 129892397)
    (by decide : 129892397 ≤ 130023469) S061C14.total S061C15.total

theorem join_1_0 : (twinPrimeSegment 127926317 128450605).card = 1987 := by
  simpa using combineTwinPrimeSegments (by decide : 127926317 ≤ 128188461)
    (by decide : 128188461 ≤ 128450605) join_0_0 join_0_1

theorem join_1_1 : (twinPrimeSegment 128450605 128974893).card = 2027 := by
  simpa using combineTwinPrimeSegments (by decide : 128450605 ≤ 128712749)
    (by decide : 128712749 ≤ 128974893) join_0_2 join_0_3

theorem join_1_2 : (twinPrimeSegment 128974893 129499181).card = 2001 := by
  simpa using combineTwinPrimeSegments (by decide : 128974893 ≤ 129237037)
    (by decide : 129237037 ≤ 129499181) join_0_4 join_0_5

theorem join_1_3 : (twinPrimeSegment 129499181 130023469).card = 2011 := by
  simpa using combineTwinPrimeSegments (by decide : 129499181 ≤ 129761325)
    (by decide : 129761325 ≤ 130023469) join_0_6 join_0_7

theorem join_2_0 : (twinPrimeSegment 127926317 128974893).card = 4014 := by
  simpa using combineTwinPrimeSegments (by decide : 127926317 ≤ 128450605)
    (by decide : 128450605 ≤ 128974893) join_1_0 join_1_1

theorem join_2_1 : (twinPrimeSegment 128974893 130023469).card = 4012 := by
  simpa using combineTwinPrimeSegments (by decide : 128974893 ≤ 129499181)
    (by decide : 129499181 ≤ 130023469) join_1_2 join_1_3

theorem join_3_0 : (twinPrimeSegment 127926317 130023469).card = 8026 := by
  simpa using combineTwinPrimeSegments (by decide : 127926317 ≤ 128974893)
    (by decide : 128974893 ≤ 130023469) join_2_0 join_2_1

theorem total : (twinPrimeSegment 127926317 130023469).card = 8026 := join_3_0

end S061All
end Sude.GeneratedTwinScan
