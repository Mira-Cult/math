import Sude.GeneratedTwinScan.S182C00
import Sude.GeneratedTwinScan.S182C01
import Sude.GeneratedTwinScan.S182C02
import Sude.GeneratedTwinScan.S182C03
import Sude.GeneratedTwinScan.S182C04
import Sude.GeneratedTwinScan.S182C05
import Sude.GeneratedTwinScan.S182C06
import Sude.GeneratedTwinScan.S182C07
import Sude.GeneratedTwinScan.S182C08
import Sude.GeneratedTwinScan.S182C09
import Sude.GeneratedTwinScan.S182C10
import Sude.GeneratedTwinScan.S182C11
import Sude.GeneratedTwinScan.S182C12
import Sude.GeneratedTwinScan.S182C13
import Sude.GeneratedTwinScan.S182C14
import Sude.GeneratedTwinScan.S182C15

/-! Combined FT source segment; Lean kernel check required. -/
namespace Sude.GeneratedTwinScan
namespace S182All

theorem join_0_0 : (twinPrimeSegment 381681709 381943853).card = 879 := by
  simpa using combineTwinPrimeSegments (by decide : 381681709 ≤ 381812781)
    (by decide : 381812781 ≤ 381943853) S182C00.total S182C01.total

theorem join_0_1 : (twinPrimeSegment 381943853 382205997).card = 885 := by
  simpa using combineTwinPrimeSegments (by decide : 381943853 ≤ 382074925)
    (by decide : 382074925 ≤ 382205997) S182C02.total S182C03.total

theorem join_0_2 : (twinPrimeSegment 382205997 382468141).card = 899 := by
  simpa using combineTwinPrimeSegments (by decide : 382205997 ≤ 382337069)
    (by decide : 382337069 ≤ 382468141) S182C04.total S182C05.total

theorem join_0_3 : (twinPrimeSegment 382468141 382730285).card = 927 := by
  simpa using combineTwinPrimeSegments (by decide : 382468141 ≤ 382599213)
    (by decide : 382599213 ≤ 382730285) S182C06.total S182C07.total

theorem join_0_4 : (twinPrimeSegment 382730285 382992429).card = 910 := by
  simpa using combineTwinPrimeSegments (by decide : 382730285 ≤ 382861357)
    (by decide : 382861357 ≤ 382992429) S182C08.total S182C09.total

theorem join_0_5 : (twinPrimeSegment 382992429 383254573).card = 890 := by
  simpa using combineTwinPrimeSegments (by decide : 382992429 ≤ 383123501)
    (by decide : 383123501 ≤ 383254573) S182C10.total S182C11.total

theorem join_0_6 : (twinPrimeSegment 383254573 383516717).card = 920 := by
  simpa using combineTwinPrimeSegments (by decide : 383254573 ≤ 383385645)
    (by decide : 383385645 ≤ 383516717) S182C12.total S182C13.total

theorem join_0_7 : (twinPrimeSegment 383516717 383778861).card = 889 := by
  simpa using combineTwinPrimeSegments (by decide : 383516717 ≤ 383647789)
    (by decide : 383647789 ≤ 383778861) S182C14.total S182C15.total

theorem join_1_0 : (twinPrimeSegment 381681709 382205997).card = 1764 := by
  simpa using combineTwinPrimeSegments (by decide : 381681709 ≤ 381943853)
    (by decide : 381943853 ≤ 382205997) join_0_0 join_0_1

theorem join_1_1 : (twinPrimeSegment 382205997 382730285).card = 1826 := by
  simpa using combineTwinPrimeSegments (by decide : 382205997 ≤ 382468141)
    (by decide : 382468141 ≤ 382730285) join_0_2 join_0_3

theorem join_1_2 : (twinPrimeSegment 382730285 383254573).card = 1800 := by
  simpa using combineTwinPrimeSegments (by decide : 382730285 ≤ 382992429)
    (by decide : 382992429 ≤ 383254573) join_0_4 join_0_5

theorem join_1_3 : (twinPrimeSegment 383254573 383778861).card = 1809 := by
  simpa using combineTwinPrimeSegments (by decide : 383254573 ≤ 383516717)
    (by decide : 383516717 ≤ 383778861) join_0_6 join_0_7

theorem join_2_0 : (twinPrimeSegment 381681709 382730285).card = 3590 := by
  simpa using combineTwinPrimeSegments (by decide : 381681709 ≤ 382205997)
    (by decide : 382205997 ≤ 382730285) join_1_0 join_1_1

theorem join_2_1 : (twinPrimeSegment 382730285 383778861).card = 3609 := by
  simpa using combineTwinPrimeSegments (by decide : 382730285 ≤ 383254573)
    (by decide : 383254573 ≤ 383778861) join_1_2 join_1_3

theorem join_3_0 : (twinPrimeSegment 381681709 383778861).card = 7199 := by
  simpa using combineTwinPrimeSegments (by decide : 381681709 ≤ 382730285)
    (by decide : 382730285 ≤ 383778861) join_2_0 join_2_1

theorem total : (twinPrimeSegment 381681709 383778861).card = 7199 := join_3_0

end S182All
end Sude.GeneratedTwinScan
