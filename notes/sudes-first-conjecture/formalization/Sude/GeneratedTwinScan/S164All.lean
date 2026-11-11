import Sude.GeneratedTwinScan.S164C00
import Sude.GeneratedTwinScan.S164C01
import Sude.GeneratedTwinScan.S164C02
import Sude.GeneratedTwinScan.S164C03
import Sude.GeneratedTwinScan.S164C04
import Sude.GeneratedTwinScan.S164C05
import Sude.GeneratedTwinScan.S164C06
import Sude.GeneratedTwinScan.S164C07
import Sude.GeneratedTwinScan.S164C08
import Sude.GeneratedTwinScan.S164C09
import Sude.GeneratedTwinScan.S164C10
import Sude.GeneratedTwinScan.S164C11
import Sude.GeneratedTwinScan.S164C12
import Sude.GeneratedTwinScan.S164C13
import Sude.GeneratedTwinScan.S164C14
import Sude.GeneratedTwinScan.S164C15

/-! Combined FT source segment; Lean kernel check required. -/
namespace Sude.GeneratedTwinScan
namespace S164All

theorem join_0_0 : (twinPrimeSegment 343932973 344195117).card = 950 := by
  simpa using combineTwinPrimeSegments (by decide : 343932973 ≤ 344064045)
    (by decide : 344064045 ≤ 344195117) S164C00.total S164C01.total

theorem join_0_1 : (twinPrimeSegment 344195117 344457261).card = 901 := by
  simpa using combineTwinPrimeSegments (by decide : 344195117 ≤ 344326189)
    (by decide : 344326189 ≤ 344457261) S164C02.total S164C03.total

theorem join_0_2 : (twinPrimeSegment 344457261 344719405).card = 906 := by
  simpa using combineTwinPrimeSegments (by decide : 344457261 ≤ 344588333)
    (by decide : 344588333 ≤ 344719405) S164C04.total S164C05.total

theorem join_0_3 : (twinPrimeSegment 344719405 344981549).card = 908 := by
  simpa using combineTwinPrimeSegments (by decide : 344719405 ≤ 344850477)
    (by decide : 344850477 ≤ 344981549) S164C06.total S164C07.total

theorem join_0_4 : (twinPrimeSegment 344981549 345243693).card = 878 := by
  simpa using combineTwinPrimeSegments (by decide : 344981549 ≤ 345112621)
    (by decide : 345112621 ≤ 345243693) S164C08.total S164C09.total

theorem join_0_5 : (twinPrimeSegment 345243693 345505837).card = 867 := by
  simpa using combineTwinPrimeSegments (by decide : 345243693 ≤ 345374765)
    (by decide : 345374765 ≤ 345505837) S164C10.total S164C11.total

theorem join_0_6 : (twinPrimeSegment 345505837 345767981).card = 896 := by
  simpa using combineTwinPrimeSegments (by decide : 345505837 ≤ 345636909)
    (by decide : 345636909 ≤ 345767981) S164C12.total S164C13.total

theorem join_0_7 : (twinPrimeSegment 345767981 346030125).card = 920 := by
  simpa using combineTwinPrimeSegments (by decide : 345767981 ≤ 345899053)
    (by decide : 345899053 ≤ 346030125) S164C14.total S164C15.total

theorem join_1_0 : (twinPrimeSegment 343932973 344457261).card = 1851 := by
  simpa using combineTwinPrimeSegments (by decide : 343932973 ≤ 344195117)
    (by decide : 344195117 ≤ 344457261) join_0_0 join_0_1

theorem join_1_1 : (twinPrimeSegment 344457261 344981549).card = 1814 := by
  simpa using combineTwinPrimeSegments (by decide : 344457261 ≤ 344719405)
    (by decide : 344719405 ≤ 344981549) join_0_2 join_0_3

theorem join_1_2 : (twinPrimeSegment 344981549 345505837).card = 1745 := by
  simpa using combineTwinPrimeSegments (by decide : 344981549 ≤ 345243693)
    (by decide : 345243693 ≤ 345505837) join_0_4 join_0_5

theorem join_1_3 : (twinPrimeSegment 345505837 346030125).card = 1816 := by
  simpa using combineTwinPrimeSegments (by decide : 345505837 ≤ 345767981)
    (by decide : 345767981 ≤ 346030125) join_0_6 join_0_7

theorem join_2_0 : (twinPrimeSegment 343932973 344981549).card = 3665 := by
  simpa using combineTwinPrimeSegments (by decide : 343932973 ≤ 344457261)
    (by decide : 344457261 ≤ 344981549) join_1_0 join_1_1

theorem join_2_1 : (twinPrimeSegment 344981549 346030125).card = 3561 := by
  simpa using combineTwinPrimeSegments (by decide : 344981549 ≤ 345505837)
    (by decide : 345505837 ≤ 346030125) join_1_2 join_1_3

theorem join_3_0 : (twinPrimeSegment 343932973 346030125).card = 7226 := by
  simpa using combineTwinPrimeSegments (by decide : 343932973 ≤ 344981549)
    (by decide : 344981549 ≤ 346030125) join_2_0 join_2_1

theorem total : (twinPrimeSegment 343932973 346030125).card = 7226 := join_3_0

end S164All
end Sude.GeneratedTwinScan
