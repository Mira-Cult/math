import Sude.GeneratedTwinScan.S233C00
import Sude.GeneratedTwinScan.S233C01
import Sude.GeneratedTwinScan.S233C02
import Sude.GeneratedTwinScan.S233C03
import Sude.GeneratedTwinScan.S233C04
import Sude.GeneratedTwinScan.S233C05
import Sude.GeneratedTwinScan.S233C06
import Sude.GeneratedTwinScan.S233C07
import Sude.GeneratedTwinScan.S233C08
import Sude.GeneratedTwinScan.S233C09
import Sude.GeneratedTwinScan.S233C10
import Sude.GeneratedTwinScan.S233C11
import Sude.GeneratedTwinScan.S233C12
import Sude.GeneratedTwinScan.S233C13
import Sude.GeneratedTwinScan.S233C14
import Sude.GeneratedTwinScan.S233C15

/-! Combined FT source segment; Lean kernel check required. -/
namespace Sude.GeneratedTwinScan
namespace S233All

theorem join_0_0 : (twinPrimeSegment 488636461 488898605).card = 857 := by
  simpa using combineTwinPrimeSegments (by decide : 488636461 ≤ 488767533)
    (by decide : 488767533 ≤ 488898605) S233C00.total S233C01.total

theorem join_0_1 : (twinPrimeSegment 488898605 489160749).card = 876 := by
  simpa using combineTwinPrimeSegments (by decide : 488898605 ≤ 489029677)
    (by decide : 489029677 ≤ 489160749) S233C02.total S233C03.total

theorem join_0_2 : (twinPrimeSegment 489160749 489422893).card = 849 := by
  simpa using combineTwinPrimeSegments (by decide : 489160749 ≤ 489291821)
    (by decide : 489291821 ≤ 489422893) S233C04.total S233C05.total

theorem join_0_3 : (twinPrimeSegment 489422893 489685037).card = 915 := by
  simpa using combineTwinPrimeSegments (by decide : 489422893 ≤ 489553965)
    (by decide : 489553965 ≤ 489685037) S233C06.total S233C07.total

theorem join_0_4 : (twinPrimeSegment 489685037 489947181).card = 867 := by
  simpa using combineTwinPrimeSegments (by decide : 489685037 ≤ 489816109)
    (by decide : 489816109 ≤ 489947181) S233C08.total S233C09.total

theorem join_0_5 : (twinPrimeSegment 489947181 490209325).card = 854 := by
  simpa using combineTwinPrimeSegments (by decide : 489947181 ≤ 490078253)
    (by decide : 490078253 ≤ 490209325) S233C10.total S233C11.total

theorem join_0_6 : (twinPrimeSegment 490209325 490471469).card = 816 := by
  simpa using combineTwinPrimeSegments (by decide : 490209325 ≤ 490340397)
    (by decide : 490340397 ≤ 490471469) S233C12.total S233C13.total

theorem join_0_7 : (twinPrimeSegment 490471469 490733613).card = 852 := by
  simpa using combineTwinPrimeSegments (by decide : 490471469 ≤ 490602541)
    (by decide : 490602541 ≤ 490733613) S233C14.total S233C15.total

theorem join_1_0 : (twinPrimeSegment 488636461 489160749).card = 1733 := by
  simpa using combineTwinPrimeSegments (by decide : 488636461 ≤ 488898605)
    (by decide : 488898605 ≤ 489160749) join_0_0 join_0_1

theorem join_1_1 : (twinPrimeSegment 489160749 489685037).card = 1764 := by
  simpa using combineTwinPrimeSegments (by decide : 489160749 ≤ 489422893)
    (by decide : 489422893 ≤ 489685037) join_0_2 join_0_3

theorem join_1_2 : (twinPrimeSegment 489685037 490209325).card = 1721 := by
  simpa using combineTwinPrimeSegments (by decide : 489685037 ≤ 489947181)
    (by decide : 489947181 ≤ 490209325) join_0_4 join_0_5

theorem join_1_3 : (twinPrimeSegment 490209325 490733613).card = 1668 := by
  simpa using combineTwinPrimeSegments (by decide : 490209325 ≤ 490471469)
    (by decide : 490471469 ≤ 490733613) join_0_6 join_0_7

theorem join_2_0 : (twinPrimeSegment 488636461 489685037).card = 3497 := by
  simpa using combineTwinPrimeSegments (by decide : 488636461 ≤ 489160749)
    (by decide : 489160749 ≤ 489685037) join_1_0 join_1_1

theorem join_2_1 : (twinPrimeSegment 489685037 490733613).card = 3389 := by
  simpa using combineTwinPrimeSegments (by decide : 489685037 ≤ 490209325)
    (by decide : 490209325 ≤ 490733613) join_1_2 join_1_3

theorem join_3_0 : (twinPrimeSegment 488636461 490733613).card = 6886 := by
  simpa using combineTwinPrimeSegments (by decide : 488636461 ≤ 489685037)
    (by decide : 489685037 ≤ 490733613) join_2_0 join_2_1

theorem total : (twinPrimeSegment 488636461 490733613).card = 6886 := join_3_0

end S233All
end Sude.GeneratedTwinScan
