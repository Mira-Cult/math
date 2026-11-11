import Sude.GeneratedTwinScan.S108C00
import Sude.GeneratedTwinScan.S108C01
import Sude.GeneratedTwinScan.S108C02
import Sude.GeneratedTwinScan.S108C03
import Sude.GeneratedTwinScan.S108C04
import Sude.GeneratedTwinScan.S108C05
import Sude.GeneratedTwinScan.S108C06
import Sude.GeneratedTwinScan.S108C07
import Sude.GeneratedTwinScan.S108C08
import Sude.GeneratedTwinScan.S108C09
import Sude.GeneratedTwinScan.S108C10
import Sude.GeneratedTwinScan.S108C11
import Sude.GeneratedTwinScan.S108C12
import Sude.GeneratedTwinScan.S108C13
import Sude.GeneratedTwinScan.S108C14
import Sude.GeneratedTwinScan.S108C15

/-! Combined FT source segment; Lean kernel check required. -/
namespace Sude.GeneratedTwinScan
namespace S108All

theorem join_0_0 : (twinPrimeSegment 226492461 226754605).card = 900 := by
  simpa using combineTwinPrimeSegments (by decide : 226492461 ≤ 226623533)
    (by decide : 226623533 ≤ 226754605) S108C00.total S108C01.total

theorem join_0_1 : (twinPrimeSegment 226754605 227016749).card = 922 := by
  simpa using combineTwinPrimeSegments (by decide : 226754605 ≤ 226885677)
    (by decide : 226885677 ≤ 227016749) S108C02.total S108C03.total

theorem join_0_2 : (twinPrimeSegment 227016749 227278893).card = 942 := by
  simpa using combineTwinPrimeSegments (by decide : 227016749 ≤ 227147821)
    (by decide : 227147821 ≤ 227278893) S108C04.total S108C05.total

theorem join_0_3 : (twinPrimeSegment 227278893 227541037).card = 951 := by
  simpa using combineTwinPrimeSegments (by decide : 227278893 ≤ 227409965)
    (by decide : 227409965 ≤ 227541037) S108C06.total S108C07.total

theorem join_0_4 : (twinPrimeSegment 227541037 227803181).card = 881 := by
  simpa using combineTwinPrimeSegments (by decide : 227541037 ≤ 227672109)
    (by decide : 227672109 ≤ 227803181) S108C08.total S108C09.total

theorem join_0_5 : (twinPrimeSegment 227803181 228065325).card = 910 := by
  simpa using combineTwinPrimeSegments (by decide : 227803181 ≤ 227934253)
    (by decide : 227934253 ≤ 228065325) S108C10.total S108C11.total

theorem join_0_6 : (twinPrimeSegment 228065325 228327469).card = 931 := by
  simpa using combineTwinPrimeSegments (by decide : 228065325 ≤ 228196397)
    (by decide : 228196397 ≤ 228327469) S108C12.total S108C13.total

theorem join_0_7 : (twinPrimeSegment 228327469 228589613).card = 924 := by
  simpa using combineTwinPrimeSegments (by decide : 228327469 ≤ 228458541)
    (by decide : 228458541 ≤ 228589613) S108C14.total S108C15.total

theorem join_1_0 : (twinPrimeSegment 226492461 227016749).card = 1822 := by
  simpa using combineTwinPrimeSegments (by decide : 226492461 ≤ 226754605)
    (by decide : 226754605 ≤ 227016749) join_0_0 join_0_1

theorem join_1_1 : (twinPrimeSegment 227016749 227541037).card = 1893 := by
  simpa using combineTwinPrimeSegments (by decide : 227016749 ≤ 227278893)
    (by decide : 227278893 ≤ 227541037) join_0_2 join_0_3

theorem join_1_2 : (twinPrimeSegment 227541037 228065325).card = 1791 := by
  simpa using combineTwinPrimeSegments (by decide : 227541037 ≤ 227803181)
    (by decide : 227803181 ≤ 228065325) join_0_4 join_0_5

theorem join_1_3 : (twinPrimeSegment 228065325 228589613).card = 1855 := by
  simpa using combineTwinPrimeSegments (by decide : 228065325 ≤ 228327469)
    (by decide : 228327469 ≤ 228589613) join_0_6 join_0_7

theorem join_2_0 : (twinPrimeSegment 226492461 227541037).card = 3715 := by
  simpa using combineTwinPrimeSegments (by decide : 226492461 ≤ 227016749)
    (by decide : 227016749 ≤ 227541037) join_1_0 join_1_1

theorem join_2_1 : (twinPrimeSegment 227541037 228589613).card = 3646 := by
  simpa using combineTwinPrimeSegments (by decide : 227541037 ≤ 228065325)
    (by decide : 228065325 ≤ 228589613) join_1_2 join_1_3

theorem join_3_0 : (twinPrimeSegment 226492461 228589613).card = 7361 := by
  simpa using combineTwinPrimeSegments (by decide : 226492461 ≤ 227541037)
    (by decide : 227541037 ≤ 228589613) join_2_0 join_2_1

theorem total : (twinPrimeSegment 226492461 228589613).card = 7361 := join_3_0

end S108All
end Sude.GeneratedTwinScan
