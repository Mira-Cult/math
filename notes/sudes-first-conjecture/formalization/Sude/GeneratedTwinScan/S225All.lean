import Sude.GeneratedTwinScan.S225C00
import Sude.GeneratedTwinScan.S225C01
import Sude.GeneratedTwinScan.S225C02
import Sude.GeneratedTwinScan.S225C03
import Sude.GeneratedTwinScan.S225C04
import Sude.GeneratedTwinScan.S225C05
import Sude.GeneratedTwinScan.S225C06
import Sude.GeneratedTwinScan.S225C07
import Sude.GeneratedTwinScan.S225C08
import Sude.GeneratedTwinScan.S225C09
import Sude.GeneratedTwinScan.S225C10
import Sude.GeneratedTwinScan.S225C11
import Sude.GeneratedTwinScan.S225C12
import Sude.GeneratedTwinScan.S225C13
import Sude.GeneratedTwinScan.S225C14
import Sude.GeneratedTwinScan.S225C15

/-! Combined FT source segment; Lean kernel check required. -/
namespace Sude.GeneratedTwinScan
namespace S225All

theorem join_0_0 : (twinPrimeSegment 471859245 472121389).card = 856 := by
  simpa using combineTwinPrimeSegments (by decide : 471859245 ≤ 471990317)
    (by decide : 471990317 ≤ 472121389) S225C00.total S225C01.total

theorem join_0_1 : (twinPrimeSegment 472121389 472383533).card = 866 := by
  simpa using combineTwinPrimeSegments (by decide : 472121389 ≤ 472252461)
    (by decide : 472252461 ≤ 472383533) S225C02.total S225C03.total

theorem join_0_2 : (twinPrimeSegment 472383533 472645677).card = 864 := by
  simpa using combineTwinPrimeSegments (by decide : 472383533 ≤ 472514605)
    (by decide : 472514605 ≤ 472645677) S225C04.total S225C05.total

theorem join_0_3 : (twinPrimeSegment 472645677 472907821).card = 815 := by
  simpa using combineTwinPrimeSegments (by decide : 472645677 ≤ 472776749)
    (by decide : 472776749 ≤ 472907821) S225C06.total S225C07.total

theorem join_0_4 : (twinPrimeSegment 472907821 473169965).card = 857 := by
  simpa using combineTwinPrimeSegments (by decide : 472907821 ≤ 473038893)
    (by decide : 473038893 ≤ 473169965) S225C08.total S225C09.total

theorem join_0_5 : (twinPrimeSegment 473169965 473432109).card = 886 := by
  simpa using combineTwinPrimeSegments (by decide : 473169965 ≤ 473301037)
    (by decide : 473301037 ≤ 473432109) S225C10.total S225C11.total

theorem join_0_6 : (twinPrimeSegment 473432109 473694253).card = 851 := by
  simpa using combineTwinPrimeSegments (by decide : 473432109 ≤ 473563181)
    (by decide : 473563181 ≤ 473694253) S225C12.total S225C13.total

theorem join_0_7 : (twinPrimeSegment 473694253 473956397).card = 865 := by
  simpa using combineTwinPrimeSegments (by decide : 473694253 ≤ 473825325)
    (by decide : 473825325 ≤ 473956397) S225C14.total S225C15.total

theorem join_1_0 : (twinPrimeSegment 471859245 472383533).card = 1722 := by
  simpa using combineTwinPrimeSegments (by decide : 471859245 ≤ 472121389)
    (by decide : 472121389 ≤ 472383533) join_0_0 join_0_1

theorem join_1_1 : (twinPrimeSegment 472383533 472907821).card = 1679 := by
  simpa using combineTwinPrimeSegments (by decide : 472383533 ≤ 472645677)
    (by decide : 472645677 ≤ 472907821) join_0_2 join_0_3

theorem join_1_2 : (twinPrimeSegment 472907821 473432109).card = 1743 := by
  simpa using combineTwinPrimeSegments (by decide : 472907821 ≤ 473169965)
    (by decide : 473169965 ≤ 473432109) join_0_4 join_0_5

theorem join_1_3 : (twinPrimeSegment 473432109 473956397).card = 1716 := by
  simpa using combineTwinPrimeSegments (by decide : 473432109 ≤ 473694253)
    (by decide : 473694253 ≤ 473956397) join_0_6 join_0_7

theorem join_2_0 : (twinPrimeSegment 471859245 472907821).card = 3401 := by
  simpa using combineTwinPrimeSegments (by decide : 471859245 ≤ 472383533)
    (by decide : 472383533 ≤ 472907821) join_1_0 join_1_1

theorem join_2_1 : (twinPrimeSegment 472907821 473956397).card = 3459 := by
  simpa using combineTwinPrimeSegments (by decide : 472907821 ≤ 473432109)
    (by decide : 473432109 ≤ 473956397) join_1_2 join_1_3

theorem join_3_0 : (twinPrimeSegment 471859245 473956397).card = 6860 := by
  simpa using combineTwinPrimeSegments (by decide : 471859245 ≤ 472907821)
    (by decide : 472907821 ≤ 473956397) join_2_0 join_2_1

theorem total : (twinPrimeSegment 471859245 473956397).card = 6860 := join_3_0

end S225All
end Sude.GeneratedTwinScan
