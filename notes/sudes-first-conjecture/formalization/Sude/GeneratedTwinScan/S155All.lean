import Sude.GeneratedTwinScan.S155C00
import Sude.GeneratedTwinScan.S155C01
import Sude.GeneratedTwinScan.S155C02
import Sude.GeneratedTwinScan.S155C03
import Sude.GeneratedTwinScan.S155C04
import Sude.GeneratedTwinScan.S155C05
import Sude.GeneratedTwinScan.S155C06
import Sude.GeneratedTwinScan.S155C07
import Sude.GeneratedTwinScan.S155C08
import Sude.GeneratedTwinScan.S155C09
import Sude.GeneratedTwinScan.S155C10
import Sude.GeneratedTwinScan.S155C11
import Sude.GeneratedTwinScan.S155C12
import Sude.GeneratedTwinScan.S155C13
import Sude.GeneratedTwinScan.S155C14
import Sude.GeneratedTwinScan.S155C15

/-! Combined FT source segment; Lean kernel check required. -/
namespace Sude.GeneratedTwinScan
namespace S155All

theorem join_0_0 : (twinPrimeSegment 325058605 325320749).card = 910 := by
  simpa using combineTwinPrimeSegments (by decide : 325058605 ≤ 325189677)
    (by decide : 325189677 ≤ 325320749) S155C00.total S155C01.total

theorem join_0_1 : (twinPrimeSegment 325320749 325582893).card = 894 := by
  simpa using combineTwinPrimeSegments (by decide : 325320749 ≤ 325451821)
    (by decide : 325451821 ≤ 325582893) S155C02.total S155C03.total

theorem join_0_2 : (twinPrimeSegment 325582893 325845037).card = 888 := by
  simpa using combineTwinPrimeSegments (by decide : 325582893 ≤ 325713965)
    (by decide : 325713965 ≤ 325845037) S155C04.total S155C05.total

theorem join_0_3 : (twinPrimeSegment 325845037 326107181).card = 911 := by
  simpa using combineTwinPrimeSegments (by decide : 325845037 ≤ 325976109)
    (by decide : 325976109 ≤ 326107181) S155C06.total S155C07.total

theorem join_0_4 : (twinPrimeSegment 326107181 326369325).card = 934 := by
  simpa using combineTwinPrimeSegments (by decide : 326107181 ≤ 326238253)
    (by decide : 326238253 ≤ 326369325) S155C08.total S155C09.total

theorem join_0_5 : (twinPrimeSegment 326369325 326631469).card = 900 := by
  simpa using combineTwinPrimeSegments (by decide : 326369325 ≤ 326500397)
    (by decide : 326500397 ≤ 326631469) S155C10.total S155C11.total

theorem join_0_6 : (twinPrimeSegment 326631469 326893613).card = 891 := by
  simpa using combineTwinPrimeSegments (by decide : 326631469 ≤ 326762541)
    (by decide : 326762541 ≤ 326893613) S155C12.total S155C13.total

theorem join_0_7 : (twinPrimeSegment 326893613 327155757).card = 896 := by
  simpa using combineTwinPrimeSegments (by decide : 326893613 ≤ 327024685)
    (by decide : 327024685 ≤ 327155757) S155C14.total S155C15.total

theorem join_1_0 : (twinPrimeSegment 325058605 325582893).card = 1804 := by
  simpa using combineTwinPrimeSegments (by decide : 325058605 ≤ 325320749)
    (by decide : 325320749 ≤ 325582893) join_0_0 join_0_1

theorem join_1_1 : (twinPrimeSegment 325582893 326107181).card = 1799 := by
  simpa using combineTwinPrimeSegments (by decide : 325582893 ≤ 325845037)
    (by decide : 325845037 ≤ 326107181) join_0_2 join_0_3

theorem join_1_2 : (twinPrimeSegment 326107181 326631469).card = 1834 := by
  simpa using combineTwinPrimeSegments (by decide : 326107181 ≤ 326369325)
    (by decide : 326369325 ≤ 326631469) join_0_4 join_0_5

theorem join_1_3 : (twinPrimeSegment 326631469 327155757).card = 1787 := by
  simpa using combineTwinPrimeSegments (by decide : 326631469 ≤ 326893613)
    (by decide : 326893613 ≤ 327155757) join_0_6 join_0_7

theorem join_2_0 : (twinPrimeSegment 325058605 326107181).card = 3603 := by
  simpa using combineTwinPrimeSegments (by decide : 325058605 ≤ 325582893)
    (by decide : 325582893 ≤ 326107181) join_1_0 join_1_1

theorem join_2_1 : (twinPrimeSegment 326107181 327155757).card = 3621 := by
  simpa using combineTwinPrimeSegments (by decide : 326107181 ≤ 326631469)
    (by decide : 326631469 ≤ 327155757) join_1_2 join_1_3

theorem join_3_0 : (twinPrimeSegment 325058605 327155757).card = 7224 := by
  simpa using combineTwinPrimeSegments (by decide : 325058605 ≤ 326107181)
    (by decide : 326107181 ≤ 327155757) join_2_0 join_2_1

theorem total : (twinPrimeSegment 325058605 327155757).card = 7224 := join_3_0

end S155All
end Sude.GeneratedTwinScan
