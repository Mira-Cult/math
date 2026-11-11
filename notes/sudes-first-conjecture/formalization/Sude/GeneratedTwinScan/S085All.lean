import Sude.GeneratedTwinScan.S085C00
import Sude.GeneratedTwinScan.S085C01
import Sude.GeneratedTwinScan.S085C02
import Sude.GeneratedTwinScan.S085C03
import Sude.GeneratedTwinScan.S085C04
import Sude.GeneratedTwinScan.S085C05
import Sude.GeneratedTwinScan.S085C06
import Sude.GeneratedTwinScan.S085C07
import Sude.GeneratedTwinScan.S085C08
import Sude.GeneratedTwinScan.S085C09
import Sude.GeneratedTwinScan.S085C10
import Sude.GeneratedTwinScan.S085C11
import Sude.GeneratedTwinScan.S085C12
import Sude.GeneratedTwinScan.S085C13
import Sude.GeneratedTwinScan.S085C14
import Sude.GeneratedTwinScan.S085C15

/-! Combined FT source segment; Lean kernel check required. -/
namespace Sude.GeneratedTwinScan
namespace S085All

theorem join_0_0 : (twinPrimeSegment 178257965 178520109).card = 913 := by
  simpa using combineTwinPrimeSegments (by decide : 178257965 ≤ 178389037)
    (by decide : 178389037 ≤ 178520109) S085C00.total S085C01.total

theorem join_0_1 : (twinPrimeSegment 178520109 178782253).card = 980 := by
  simpa using combineTwinPrimeSegments (by decide : 178520109 ≤ 178651181)
    (by decide : 178651181 ≤ 178782253) S085C02.total S085C03.total

theorem join_0_2 : (twinPrimeSegment 178782253 179044397).card = 975 := by
  simpa using combineTwinPrimeSegments (by decide : 178782253 ≤ 178913325)
    (by decide : 178913325 ≤ 179044397) S085C04.total S085C05.total

theorem join_0_3 : (twinPrimeSegment 179044397 179306541).card = 951 := by
  simpa using combineTwinPrimeSegments (by decide : 179044397 ≤ 179175469)
    (by decide : 179175469 ≤ 179306541) S085C06.total S085C07.total

theorem join_0_4 : (twinPrimeSegment 179306541 179568685).card = 973 := by
  simpa using combineTwinPrimeSegments (by decide : 179306541 ≤ 179437613)
    (by decide : 179437613 ≤ 179568685) S085C08.total S085C09.total

theorem join_0_5 : (twinPrimeSegment 179568685 179830829).card = 990 := by
  simpa using combineTwinPrimeSegments (by decide : 179568685 ≤ 179699757)
    (by decide : 179699757 ≤ 179830829) S085C10.total S085C11.total

theorem join_0_6 : (twinPrimeSegment 179830829 180092973).card = 918 := by
  simpa using combineTwinPrimeSegments (by decide : 179830829 ≤ 179961901)
    (by decide : 179961901 ≤ 180092973) S085C12.total S085C13.total

theorem join_0_7 : (twinPrimeSegment 180092973 180355117).card = 951 := by
  simpa using combineTwinPrimeSegments (by decide : 180092973 ≤ 180224045)
    (by decide : 180224045 ≤ 180355117) S085C14.total S085C15.total

theorem join_1_0 : (twinPrimeSegment 178257965 178782253).card = 1893 := by
  simpa using combineTwinPrimeSegments (by decide : 178257965 ≤ 178520109)
    (by decide : 178520109 ≤ 178782253) join_0_0 join_0_1

theorem join_1_1 : (twinPrimeSegment 178782253 179306541).card = 1926 := by
  simpa using combineTwinPrimeSegments (by decide : 178782253 ≤ 179044397)
    (by decide : 179044397 ≤ 179306541) join_0_2 join_0_3

theorem join_1_2 : (twinPrimeSegment 179306541 179830829).card = 1963 := by
  simpa using combineTwinPrimeSegments (by decide : 179306541 ≤ 179568685)
    (by decide : 179568685 ≤ 179830829) join_0_4 join_0_5

theorem join_1_3 : (twinPrimeSegment 179830829 180355117).card = 1869 := by
  simpa using combineTwinPrimeSegments (by decide : 179830829 ≤ 180092973)
    (by decide : 180092973 ≤ 180355117) join_0_6 join_0_7

theorem join_2_0 : (twinPrimeSegment 178257965 179306541).card = 3819 := by
  simpa using combineTwinPrimeSegments (by decide : 178257965 ≤ 178782253)
    (by decide : 178782253 ≤ 179306541) join_1_0 join_1_1

theorem join_2_1 : (twinPrimeSegment 179306541 180355117).card = 3832 := by
  simpa using combineTwinPrimeSegments (by decide : 179306541 ≤ 179830829)
    (by decide : 179830829 ≤ 180355117) join_1_2 join_1_3

theorem join_3_0 : (twinPrimeSegment 178257965 180355117).card = 7651 := by
  simpa using combineTwinPrimeSegments (by decide : 178257965 ≤ 179306541)
    (by decide : 179306541 ≤ 180355117) join_2_0 join_2_1

theorem total : (twinPrimeSegment 178257965 180355117).card = 7651 := join_3_0

end S085All
end Sude.GeneratedTwinScan
