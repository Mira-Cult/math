import Sude.GeneratedTwinScan.S163C00
import Sude.GeneratedTwinScan.S163C01
import Sude.GeneratedTwinScan.S163C02
import Sude.GeneratedTwinScan.S163C03
import Sude.GeneratedTwinScan.S163C04
import Sude.GeneratedTwinScan.S163C05
import Sude.GeneratedTwinScan.S163C06
import Sude.GeneratedTwinScan.S163C07
import Sude.GeneratedTwinScan.S163C08
import Sude.GeneratedTwinScan.S163C09
import Sude.GeneratedTwinScan.S163C10
import Sude.GeneratedTwinScan.S163C11
import Sude.GeneratedTwinScan.S163C12
import Sude.GeneratedTwinScan.S163C13
import Sude.GeneratedTwinScan.S163C14
import Sude.GeneratedTwinScan.S163C15

/-! Combined FT source segment; Lean kernel check required. -/
namespace Sude.GeneratedTwinScan
namespace S163All

theorem join_0_0 : (twinPrimeSegment 341835821 342097965).card = 940 := by
  simpa using combineTwinPrimeSegments (by decide : 341835821 ≤ 341966893)
    (by decide : 341966893 ≤ 342097965) S163C00.total S163C01.total

theorem join_0_1 : (twinPrimeSegment 342097965 342360109).card = 871 := by
  simpa using combineTwinPrimeSegments (by decide : 342097965 ≤ 342229037)
    (by decide : 342229037 ≤ 342360109) S163C02.total S163C03.total

theorem join_0_2 : (twinPrimeSegment 342360109 342622253).card = 901 := by
  simpa using combineTwinPrimeSegments (by decide : 342360109 ≤ 342491181)
    (by decide : 342491181 ≤ 342622253) S163C04.total S163C05.total

theorem join_0_3 : (twinPrimeSegment 342622253 342884397).card = 906 := by
  simpa using combineTwinPrimeSegments (by decide : 342622253 ≤ 342753325)
    (by decide : 342753325 ≤ 342884397) S163C06.total S163C07.total

theorem join_0_4 : (twinPrimeSegment 342884397 343146541).card = 879 := by
  simpa using combineTwinPrimeSegments (by decide : 342884397 ≤ 343015469)
    (by decide : 343015469 ≤ 343146541) S163C08.total S163C09.total

theorem join_0_5 : (twinPrimeSegment 343146541 343408685).card = 864 := by
  simpa using combineTwinPrimeSegments (by decide : 343146541 ≤ 343277613)
    (by decide : 343277613 ≤ 343408685) S163C10.total S163C11.total

theorem join_0_6 : (twinPrimeSegment 343408685 343670829).card = 920 := by
  simpa using combineTwinPrimeSegments (by decide : 343408685 ≤ 343539757)
    (by decide : 343539757 ≤ 343670829) S163C12.total S163C13.total

theorem join_0_7 : (twinPrimeSegment 343670829 343932973).card = 923 := by
  simpa using combineTwinPrimeSegments (by decide : 343670829 ≤ 343801901)
    (by decide : 343801901 ≤ 343932973) S163C14.total S163C15.total

theorem join_1_0 : (twinPrimeSegment 341835821 342360109).card = 1811 := by
  simpa using combineTwinPrimeSegments (by decide : 341835821 ≤ 342097965)
    (by decide : 342097965 ≤ 342360109) join_0_0 join_0_1

theorem join_1_1 : (twinPrimeSegment 342360109 342884397).card = 1807 := by
  simpa using combineTwinPrimeSegments (by decide : 342360109 ≤ 342622253)
    (by decide : 342622253 ≤ 342884397) join_0_2 join_0_3

theorem join_1_2 : (twinPrimeSegment 342884397 343408685).card = 1743 := by
  simpa using combineTwinPrimeSegments (by decide : 342884397 ≤ 343146541)
    (by decide : 343146541 ≤ 343408685) join_0_4 join_0_5

theorem join_1_3 : (twinPrimeSegment 343408685 343932973).card = 1843 := by
  simpa using combineTwinPrimeSegments (by decide : 343408685 ≤ 343670829)
    (by decide : 343670829 ≤ 343932973) join_0_6 join_0_7

theorem join_2_0 : (twinPrimeSegment 341835821 342884397).card = 3618 := by
  simpa using combineTwinPrimeSegments (by decide : 341835821 ≤ 342360109)
    (by decide : 342360109 ≤ 342884397) join_1_0 join_1_1

theorem join_2_1 : (twinPrimeSegment 342884397 343932973).card = 3586 := by
  simpa using combineTwinPrimeSegments (by decide : 342884397 ≤ 343408685)
    (by decide : 343408685 ≤ 343932973) join_1_2 join_1_3

theorem join_3_0 : (twinPrimeSegment 341835821 343932973).card = 7204 := by
  simpa using combineTwinPrimeSegments (by decide : 341835821 ≤ 342884397)
    (by decide : 342884397 ≤ 343932973) join_2_0 join_2_1

theorem total : (twinPrimeSegment 341835821 343932973).card = 7204 := join_3_0

end S163All
end Sude.GeneratedTwinScan
