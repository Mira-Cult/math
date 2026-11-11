import Sude.GeneratedTwinScan.S053C00
import Sude.GeneratedTwinScan.S053C01
import Sude.GeneratedTwinScan.S053C02
import Sude.GeneratedTwinScan.S053C03
import Sude.GeneratedTwinScan.S053C04
import Sude.GeneratedTwinScan.S053C05
import Sude.GeneratedTwinScan.S053C06
import Sude.GeneratedTwinScan.S053C07
import Sude.GeneratedTwinScan.S053C08
import Sude.GeneratedTwinScan.S053C09
import Sude.GeneratedTwinScan.S053C10
import Sude.GeneratedTwinScan.S053C11
import Sude.GeneratedTwinScan.S053C12
import Sude.GeneratedTwinScan.S053C13
import Sude.GeneratedTwinScan.S053C14
import Sude.GeneratedTwinScan.S053C15

/-! Combined FT source segment; Lean kernel check required. -/
namespace Sude.GeneratedTwinScan
namespace S053All

theorem join_0_0 : (twinPrimeSegment 111149101 111411245).card = 998 := by
  simpa using combineTwinPrimeSegments (by decide : 111149101 ≤ 111280173)
    (by decide : 111280173 ≤ 111411245) S053C00.total S053C01.total

theorem join_0_1 : (twinPrimeSegment 111411245 111673389).card = 989 := by
  simpa using combineTwinPrimeSegments (by decide : 111411245 ≤ 111542317)
    (by decide : 111542317 ≤ 111673389) S053C02.total S053C03.total

theorem join_0_2 : (twinPrimeSegment 111673389 111935533).card = 1021 := by
  simpa using combineTwinPrimeSegments (by decide : 111673389 ≤ 111804461)
    (by decide : 111804461 ≤ 111935533) S053C04.total S053C05.total

theorem join_0_3 : (twinPrimeSegment 111935533 112197677).card = 991 := by
  simpa using combineTwinPrimeSegments (by decide : 111935533 ≤ 112066605)
    (by decide : 112066605 ≤ 112197677) S053C06.total S053C07.total

theorem join_0_4 : (twinPrimeSegment 112197677 112459821).card = 983 := by
  simpa using combineTwinPrimeSegments (by decide : 112197677 ≤ 112328749)
    (by decide : 112328749 ≤ 112459821) S053C08.total S053C09.total

theorem join_0_5 : (twinPrimeSegment 112459821 112721965).card = 1003 := by
  simpa using combineTwinPrimeSegments (by decide : 112459821 ≤ 112590893)
    (by decide : 112590893 ≤ 112721965) S053C10.total S053C11.total

theorem join_0_6 : (twinPrimeSegment 112721965 112984109).card = 1020 := by
  simpa using combineTwinPrimeSegments (by decide : 112721965 ≤ 112853037)
    (by decide : 112853037 ≤ 112984109) S053C12.total S053C13.total

theorem join_0_7 : (twinPrimeSegment 112984109 113246253).card = 979 := by
  simpa using combineTwinPrimeSegments (by decide : 112984109 ≤ 113115181)
    (by decide : 113115181 ≤ 113246253) S053C14.total S053C15.total

theorem join_1_0 : (twinPrimeSegment 111149101 111673389).card = 1987 := by
  simpa using combineTwinPrimeSegments (by decide : 111149101 ≤ 111411245)
    (by decide : 111411245 ≤ 111673389) join_0_0 join_0_1

theorem join_1_1 : (twinPrimeSegment 111673389 112197677).card = 2012 := by
  simpa using combineTwinPrimeSegments (by decide : 111673389 ≤ 111935533)
    (by decide : 111935533 ≤ 112197677) join_0_2 join_0_3

theorem join_1_2 : (twinPrimeSegment 112197677 112721965).card = 1986 := by
  simpa using combineTwinPrimeSegments (by decide : 112197677 ≤ 112459821)
    (by decide : 112459821 ≤ 112721965) join_0_4 join_0_5

theorem join_1_3 : (twinPrimeSegment 112721965 113246253).card = 1999 := by
  simpa using combineTwinPrimeSegments (by decide : 112721965 ≤ 112984109)
    (by decide : 112984109 ≤ 113246253) join_0_6 join_0_7

theorem join_2_0 : (twinPrimeSegment 111149101 112197677).card = 3999 := by
  simpa using combineTwinPrimeSegments (by decide : 111149101 ≤ 111673389)
    (by decide : 111673389 ≤ 112197677) join_1_0 join_1_1

theorem join_2_1 : (twinPrimeSegment 112197677 113246253).card = 3985 := by
  simpa using combineTwinPrimeSegments (by decide : 112197677 ≤ 112721965)
    (by decide : 112721965 ≤ 113246253) join_1_2 join_1_3

theorem join_3_0 : (twinPrimeSegment 111149101 113246253).card = 7984 := by
  simpa using combineTwinPrimeSegments (by decide : 111149101 ≤ 112197677)
    (by decide : 112197677 ≤ 113246253) join_2_0 join_2_1

theorem total : (twinPrimeSegment 111149101 113246253).card = 7984 := join_3_0

end S053All
end Sude.GeneratedTwinScan
