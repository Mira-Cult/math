import Sude.GeneratedTwinScan.S069C00
import Sude.GeneratedTwinScan.S069C01
import Sude.GeneratedTwinScan.S069C02
import Sude.GeneratedTwinScan.S069C03
import Sude.GeneratedTwinScan.S069C04
import Sude.GeneratedTwinScan.S069C05
import Sude.GeneratedTwinScan.S069C06
import Sude.GeneratedTwinScan.S069C07
import Sude.GeneratedTwinScan.S069C08
import Sude.GeneratedTwinScan.S069C09
import Sude.GeneratedTwinScan.S069C10
import Sude.GeneratedTwinScan.S069C11
import Sude.GeneratedTwinScan.S069C12
import Sude.GeneratedTwinScan.S069C13
import Sude.GeneratedTwinScan.S069C14
import Sude.GeneratedTwinScan.S069C15

/-! Combined FT source segment; Lean kernel check required. -/
namespace Sude.GeneratedTwinScan
namespace S069All

theorem join_0_0 : (twinPrimeSegment 144703533 144965677).card = 950 := by
  simpa using combineTwinPrimeSegments (by decide : 144703533 ≤ 144834605)
    (by decide : 144834605 ≤ 144965677) S069C00.total S069C01.total

theorem join_0_1 : (twinPrimeSegment 144965677 145227821).card = 974 := by
  simpa using combineTwinPrimeSegments (by decide : 144965677 ≤ 145096749)
    (by decide : 145096749 ≤ 145227821) S069C02.total S069C03.total

theorem join_0_2 : (twinPrimeSegment 145227821 145489965).card = 919 := by
  simpa using combineTwinPrimeSegments (by decide : 145227821 ≤ 145358893)
    (by decide : 145358893 ≤ 145489965) S069C04.total S069C05.total

theorem join_0_3 : (twinPrimeSegment 145489965 145752109).card = 1015 := by
  simpa using combineTwinPrimeSegments (by decide : 145489965 ≤ 145621037)
    (by decide : 145621037 ≤ 145752109) S069C06.total S069C07.total

theorem join_0_4 : (twinPrimeSegment 145752109 146014253).card = 986 := by
  simpa using combineTwinPrimeSegments (by decide : 145752109 ≤ 145883181)
    (by decide : 145883181 ≤ 146014253) S069C08.total S069C09.total

theorem join_0_5 : (twinPrimeSegment 146014253 146276397).card = 986 := by
  simpa using combineTwinPrimeSegments (by decide : 146014253 ≤ 146145325)
    (by decide : 146145325 ≤ 146276397) S069C10.total S069C11.total

theorem join_0_6 : (twinPrimeSegment 146276397 146538541).card = 948 := by
  simpa using combineTwinPrimeSegments (by decide : 146276397 ≤ 146407469)
    (by decide : 146407469 ≤ 146538541) S069C12.total S069C13.total

theorem join_0_7 : (twinPrimeSegment 146538541 146800685).card = 988 := by
  simpa using combineTwinPrimeSegments (by decide : 146538541 ≤ 146669613)
    (by decide : 146669613 ≤ 146800685) S069C14.total S069C15.total

theorem join_1_0 : (twinPrimeSegment 144703533 145227821).card = 1924 := by
  simpa using combineTwinPrimeSegments (by decide : 144703533 ≤ 144965677)
    (by decide : 144965677 ≤ 145227821) join_0_0 join_0_1

theorem join_1_1 : (twinPrimeSegment 145227821 145752109).card = 1934 := by
  simpa using combineTwinPrimeSegments (by decide : 145227821 ≤ 145489965)
    (by decide : 145489965 ≤ 145752109) join_0_2 join_0_3

theorem join_1_2 : (twinPrimeSegment 145752109 146276397).card = 1972 := by
  simpa using combineTwinPrimeSegments (by decide : 145752109 ≤ 146014253)
    (by decide : 146014253 ≤ 146276397) join_0_4 join_0_5

theorem join_1_3 : (twinPrimeSegment 146276397 146800685).card = 1936 := by
  simpa using combineTwinPrimeSegments (by decide : 146276397 ≤ 146538541)
    (by decide : 146538541 ≤ 146800685) join_0_6 join_0_7

theorem join_2_0 : (twinPrimeSegment 144703533 145752109).card = 3858 := by
  simpa using combineTwinPrimeSegments (by decide : 144703533 ≤ 145227821)
    (by decide : 145227821 ≤ 145752109) join_1_0 join_1_1

theorem join_2_1 : (twinPrimeSegment 145752109 146800685).card = 3908 := by
  simpa using combineTwinPrimeSegments (by decide : 145752109 ≤ 146276397)
    (by decide : 146276397 ≤ 146800685) join_1_2 join_1_3

theorem join_3_0 : (twinPrimeSegment 144703533 146800685).card = 7766 := by
  simpa using combineTwinPrimeSegments (by decide : 144703533 ≤ 145752109)
    (by decide : 145752109 ≤ 146800685) join_2_0 join_2_1

theorem total : (twinPrimeSegment 144703533 146800685).card = 7766 := join_3_0

end S069All
end Sude.GeneratedTwinScan
