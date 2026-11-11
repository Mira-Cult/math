import Sude.GeneratedTwinScan.S139C00
import Sude.GeneratedTwinScan.S139C01
import Sude.GeneratedTwinScan.S139C02
import Sude.GeneratedTwinScan.S139C03
import Sude.GeneratedTwinScan.S139C04
import Sude.GeneratedTwinScan.S139C05
import Sude.GeneratedTwinScan.S139C06
import Sude.GeneratedTwinScan.S139C07
import Sude.GeneratedTwinScan.S139C08
import Sude.GeneratedTwinScan.S139C09
import Sude.GeneratedTwinScan.S139C10
import Sude.GeneratedTwinScan.S139C11
import Sude.GeneratedTwinScan.S139C12
import Sude.GeneratedTwinScan.S139C13
import Sude.GeneratedTwinScan.S139C14
import Sude.GeneratedTwinScan.S139C15

/-! Combined FT source segment; Lean kernel check required. -/
namespace Sude.GeneratedTwinScan
namespace S139All

theorem join_0_0 : (twinPrimeSegment 291504173 291766317).card = 884 := by
  simpa using combineTwinPrimeSegments (by decide : 291504173 ≤ 291635245)
    (by decide : 291635245 ≤ 291766317) S139C00.total S139C01.total

theorem join_0_1 : (twinPrimeSegment 291766317 292028461).card = 939 := by
  simpa using combineTwinPrimeSegments (by decide : 291766317 ≤ 291897389)
    (by decide : 291897389 ≤ 292028461) S139C02.total S139C03.total

theorem join_0_2 : (twinPrimeSegment 292028461 292290605).card = 922 := by
  simpa using combineTwinPrimeSegments (by decide : 292028461 ≤ 292159533)
    (by decide : 292159533 ≤ 292290605) S139C04.total S139C05.total

theorem join_0_3 : (twinPrimeSegment 292290605 292552749).card = 902 := by
  simpa using combineTwinPrimeSegments (by decide : 292290605 ≤ 292421677)
    (by decide : 292421677 ≤ 292552749) S139C06.total S139C07.total

theorem join_0_4 : (twinPrimeSegment 292552749 292814893).card = 948 := by
  simpa using combineTwinPrimeSegments (by decide : 292552749 ≤ 292683821)
    (by decide : 292683821 ≤ 292814893) S139C08.total S139C09.total

theorem join_0_5 : (twinPrimeSegment 292814893 293077037).card = 918 := by
  simpa using combineTwinPrimeSegments (by decide : 292814893 ≤ 292945965)
    (by decide : 292945965 ≤ 293077037) S139C10.total S139C11.total

theorem join_0_6 : (twinPrimeSegment 293077037 293339181).card = 908 := by
  simpa using combineTwinPrimeSegments (by decide : 293077037 ≤ 293208109)
    (by decide : 293208109 ≤ 293339181) S139C12.total S139C13.total

theorem join_0_7 : (twinPrimeSegment 293339181 293601325).card = 917 := by
  simpa using combineTwinPrimeSegments (by decide : 293339181 ≤ 293470253)
    (by decide : 293470253 ≤ 293601325) S139C14.total S139C15.total

theorem join_1_0 : (twinPrimeSegment 291504173 292028461).card = 1823 := by
  simpa using combineTwinPrimeSegments (by decide : 291504173 ≤ 291766317)
    (by decide : 291766317 ≤ 292028461) join_0_0 join_0_1

theorem join_1_1 : (twinPrimeSegment 292028461 292552749).card = 1824 := by
  simpa using combineTwinPrimeSegments (by decide : 292028461 ≤ 292290605)
    (by decide : 292290605 ≤ 292552749) join_0_2 join_0_3

theorem join_1_2 : (twinPrimeSegment 292552749 293077037).card = 1866 := by
  simpa using combineTwinPrimeSegments (by decide : 292552749 ≤ 292814893)
    (by decide : 292814893 ≤ 293077037) join_0_4 join_0_5

theorem join_1_3 : (twinPrimeSegment 293077037 293601325).card = 1825 := by
  simpa using combineTwinPrimeSegments (by decide : 293077037 ≤ 293339181)
    (by decide : 293339181 ≤ 293601325) join_0_6 join_0_7

theorem join_2_0 : (twinPrimeSegment 291504173 292552749).card = 3647 := by
  simpa using combineTwinPrimeSegments (by decide : 291504173 ≤ 292028461)
    (by decide : 292028461 ≤ 292552749) join_1_0 join_1_1

theorem join_2_1 : (twinPrimeSegment 292552749 293601325).card = 3691 := by
  simpa using combineTwinPrimeSegments (by decide : 292552749 ≤ 293077037)
    (by decide : 293077037 ≤ 293601325) join_1_2 join_1_3

theorem join_3_0 : (twinPrimeSegment 291504173 293601325).card = 7338 := by
  simpa using combineTwinPrimeSegments (by decide : 291504173 ≤ 292552749)
    (by decide : 292552749 ≤ 293601325) join_2_0 join_2_1

theorem total : (twinPrimeSegment 291504173 293601325).card = 7338 := join_3_0

end S139All
end Sude.GeneratedTwinScan
