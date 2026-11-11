import Sude.GeneratedTwinScan.S116C00
import Sude.GeneratedTwinScan.S116C01
import Sude.GeneratedTwinScan.S116C02
import Sude.GeneratedTwinScan.S116C03
import Sude.GeneratedTwinScan.S116C04
import Sude.GeneratedTwinScan.S116C05
import Sude.GeneratedTwinScan.S116C06
import Sude.GeneratedTwinScan.S116C07
import Sude.GeneratedTwinScan.S116C08
import Sude.GeneratedTwinScan.S116C09
import Sude.GeneratedTwinScan.S116C10
import Sude.GeneratedTwinScan.S116C11
import Sude.GeneratedTwinScan.S116C12
import Sude.GeneratedTwinScan.S116C13
import Sude.GeneratedTwinScan.S116C14
import Sude.GeneratedTwinScan.S116C15

/-! Combined FT source segment; Lean kernel check required. -/
namespace Sude.GeneratedTwinScan
namespace S116All

theorem join_0_0 : (twinPrimeSegment 243269677 243531821).card = 936 := by
  simpa using combineTwinPrimeSegments (by decide : 243269677 ≤ 243400749)
    (by decide : 243400749 ≤ 243531821) S116C00.total S116C01.total

theorem join_0_1 : (twinPrimeSegment 243531821 243793965).card = 915 := by
  simpa using combineTwinPrimeSegments (by decide : 243531821 ≤ 243662893)
    (by decide : 243662893 ≤ 243793965) S116C02.total S116C03.total

theorem join_0_2 : (twinPrimeSegment 243793965 244056109).card = 949 := by
  simpa using combineTwinPrimeSegments (by decide : 243793965 ≤ 243925037)
    (by decide : 243925037 ≤ 244056109) S116C04.total S116C05.total

theorem join_0_3 : (twinPrimeSegment 244056109 244318253).card = 942 := by
  simpa using combineTwinPrimeSegments (by decide : 244056109 ≤ 244187181)
    (by decide : 244187181 ≤ 244318253) S116C06.total S116C07.total

theorem join_0_4 : (twinPrimeSegment 244318253 244580397).card = 931 := by
  simpa using combineTwinPrimeSegments (by decide : 244318253 ≤ 244449325)
    (by decide : 244449325 ≤ 244580397) S116C08.total S116C09.total

theorem join_0_5 : (twinPrimeSegment 244580397 244842541).card = 946 := by
  simpa using combineTwinPrimeSegments (by decide : 244580397 ≤ 244711469)
    (by decide : 244711469 ≤ 244842541) S116C10.total S116C11.total

theorem join_0_6 : (twinPrimeSegment 244842541 245104685).card = 942 := by
  simpa using combineTwinPrimeSegments (by decide : 244842541 ≤ 244973613)
    (by decide : 244973613 ≤ 245104685) S116C12.total S116C13.total

theorem join_0_7 : (twinPrimeSegment 245104685 245366829).card = 919 := by
  simpa using combineTwinPrimeSegments (by decide : 245104685 ≤ 245235757)
    (by decide : 245235757 ≤ 245366829) S116C14.total S116C15.total

theorem join_1_0 : (twinPrimeSegment 243269677 243793965).card = 1851 := by
  simpa using combineTwinPrimeSegments (by decide : 243269677 ≤ 243531821)
    (by decide : 243531821 ≤ 243793965) join_0_0 join_0_1

theorem join_1_1 : (twinPrimeSegment 243793965 244318253).card = 1891 := by
  simpa using combineTwinPrimeSegments (by decide : 243793965 ≤ 244056109)
    (by decide : 244056109 ≤ 244318253) join_0_2 join_0_3

theorem join_1_2 : (twinPrimeSegment 244318253 244842541).card = 1877 := by
  simpa using combineTwinPrimeSegments (by decide : 244318253 ≤ 244580397)
    (by decide : 244580397 ≤ 244842541) join_0_4 join_0_5

theorem join_1_3 : (twinPrimeSegment 244842541 245366829).card = 1861 := by
  simpa using combineTwinPrimeSegments (by decide : 244842541 ≤ 245104685)
    (by decide : 245104685 ≤ 245366829) join_0_6 join_0_7

theorem join_2_0 : (twinPrimeSegment 243269677 244318253).card = 3742 := by
  simpa using combineTwinPrimeSegments (by decide : 243269677 ≤ 243793965)
    (by decide : 243793965 ≤ 244318253) join_1_0 join_1_1

theorem join_2_1 : (twinPrimeSegment 244318253 245366829).card = 3738 := by
  simpa using combineTwinPrimeSegments (by decide : 244318253 ≤ 244842541)
    (by decide : 244842541 ≤ 245366829) join_1_2 join_1_3

theorem join_3_0 : (twinPrimeSegment 243269677 245366829).card = 7480 := by
  simpa using combineTwinPrimeSegments (by decide : 243269677 ≤ 244318253)
    (by decide : 244318253 ≤ 245366829) join_2_0 join_2_1

theorem total : (twinPrimeSegment 243269677 245366829).card = 7480 := join_3_0

end S116All
end Sude.GeneratedTwinScan
