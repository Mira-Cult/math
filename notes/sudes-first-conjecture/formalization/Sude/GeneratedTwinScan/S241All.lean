import Sude.GeneratedTwinScan.S241C00
import Sude.GeneratedTwinScan.S241C01
import Sude.GeneratedTwinScan.S241C02
import Sude.GeneratedTwinScan.S241C03
import Sude.GeneratedTwinScan.S241C04
import Sude.GeneratedTwinScan.S241C05
import Sude.GeneratedTwinScan.S241C06
import Sude.GeneratedTwinScan.S241C07
import Sude.GeneratedTwinScan.S241C08
import Sude.GeneratedTwinScan.S241C09
import Sude.GeneratedTwinScan.S241C10
import Sude.GeneratedTwinScan.S241C11
import Sude.GeneratedTwinScan.S241C12
import Sude.GeneratedTwinScan.S241C13
import Sude.GeneratedTwinScan.S241C14
import Sude.GeneratedTwinScan.S241C15

/-! Combined FT source segment; Lean kernel check required. -/
namespace Sude.GeneratedTwinScan
namespace S241All

theorem join_0_0 : (twinPrimeSegment 505413677 505675821).card = 866 := by
  simpa using combineTwinPrimeSegments (by decide : 505413677 ≤ 505544749)
    (by decide : 505544749 ≤ 505675821) S241C00.total S241C01.total

theorem join_0_1 : (twinPrimeSegment 505675821 505937965).card = 906 := by
  simpa using combineTwinPrimeSegments (by decide : 505675821 ≤ 505806893)
    (by decide : 505806893 ≤ 505937965) S241C02.total S241C03.total

theorem join_0_2 : (twinPrimeSegment 505937965 506200109).card = 894 := by
  simpa using combineTwinPrimeSegments (by decide : 505937965 ≤ 506069037)
    (by decide : 506069037 ≤ 506200109) S241C04.total S241C05.total

theorem join_0_3 : (twinPrimeSegment 506200109 506462253).card = 851 := by
  simpa using combineTwinPrimeSegments (by decide : 506200109 ≤ 506331181)
    (by decide : 506331181 ≤ 506462253) S241C06.total S241C07.total

theorem join_0_4 : (twinPrimeSegment 506462253 506724397).card = 804 := by
  simpa using combineTwinPrimeSegments (by decide : 506462253 ≤ 506593325)
    (by decide : 506593325 ≤ 506724397) S241C08.total S241C09.total

theorem join_0_5 : (twinPrimeSegment 506724397 506986541).card = 826 := by
  simpa using combineTwinPrimeSegments (by decide : 506724397 ≤ 506855469)
    (by decide : 506855469 ≤ 506986541) S241C10.total S241C11.total

theorem join_0_6 : (twinPrimeSegment 506986541 507248685).card = 859 := by
  simpa using combineTwinPrimeSegments (by decide : 506986541 ≤ 507117613)
    (by decide : 507117613 ≤ 507248685) S241C12.total S241C13.total

theorem join_0_7 : (twinPrimeSegment 507248685 507510829).card = 876 := by
  simpa using combineTwinPrimeSegments (by decide : 507248685 ≤ 507379757)
    (by decide : 507379757 ≤ 507510829) S241C14.total S241C15.total

theorem join_1_0 : (twinPrimeSegment 505413677 505937965).card = 1772 := by
  simpa using combineTwinPrimeSegments (by decide : 505413677 ≤ 505675821)
    (by decide : 505675821 ≤ 505937965) join_0_0 join_0_1

theorem join_1_1 : (twinPrimeSegment 505937965 506462253).card = 1745 := by
  simpa using combineTwinPrimeSegments (by decide : 505937965 ≤ 506200109)
    (by decide : 506200109 ≤ 506462253) join_0_2 join_0_3

theorem join_1_2 : (twinPrimeSegment 506462253 506986541).card = 1630 := by
  simpa using combineTwinPrimeSegments (by decide : 506462253 ≤ 506724397)
    (by decide : 506724397 ≤ 506986541) join_0_4 join_0_5

theorem join_1_3 : (twinPrimeSegment 506986541 507510829).card = 1735 := by
  simpa using combineTwinPrimeSegments (by decide : 506986541 ≤ 507248685)
    (by decide : 507248685 ≤ 507510829) join_0_6 join_0_7

theorem join_2_0 : (twinPrimeSegment 505413677 506462253).card = 3517 := by
  simpa using combineTwinPrimeSegments (by decide : 505413677 ≤ 505937965)
    (by decide : 505937965 ≤ 506462253) join_1_0 join_1_1

theorem join_2_1 : (twinPrimeSegment 506462253 507510829).card = 3365 := by
  simpa using combineTwinPrimeSegments (by decide : 506462253 ≤ 506986541)
    (by decide : 506986541 ≤ 507510829) join_1_2 join_1_3

theorem join_3_0 : (twinPrimeSegment 505413677 507510829).card = 6882 := by
  simpa using combineTwinPrimeSegments (by decide : 505413677 ≤ 506462253)
    (by decide : 506462253 ≤ 507510829) join_2_0 join_2_1

theorem total : (twinPrimeSegment 505413677 507510829).card = 6882 := join_3_0

end S241All
end Sude.GeneratedTwinScan
