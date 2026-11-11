import Sude.GeneratedTwinScan.S221C00
import Sude.GeneratedTwinScan.S221C01
import Sude.GeneratedTwinScan.S221C02
import Sude.GeneratedTwinScan.S221C03
import Sude.GeneratedTwinScan.S221C04
import Sude.GeneratedTwinScan.S221C05
import Sude.GeneratedTwinScan.S221C06
import Sude.GeneratedTwinScan.S221C07
import Sude.GeneratedTwinScan.S221C08
import Sude.GeneratedTwinScan.S221C09
import Sude.GeneratedTwinScan.S221C10
import Sude.GeneratedTwinScan.S221C11
import Sude.GeneratedTwinScan.S221C12
import Sude.GeneratedTwinScan.S221C13
import Sude.GeneratedTwinScan.S221C14
import Sude.GeneratedTwinScan.S221C15

/-! Combined FT source segment; Lean kernel check required. -/
namespace Sude.GeneratedTwinScan
namespace S221All

theorem join_0_0 : (twinPrimeSegment 463470637 463732781).card = 821 := by
  simpa using combineTwinPrimeSegments (by decide : 463470637 ≤ 463601709)
    (by decide : 463601709 ≤ 463732781) S221C00.total S221C01.total

theorem join_0_1 : (twinPrimeSegment 463732781 463994925).card = 884 := by
  simpa using combineTwinPrimeSegments (by decide : 463732781 ≤ 463863853)
    (by decide : 463863853 ≤ 463994925) S221C02.total S221C03.total

theorem join_0_2 : (twinPrimeSegment 463994925 464257069).card = 856 := by
  simpa using combineTwinPrimeSegments (by decide : 463994925 ≤ 464125997)
    (by decide : 464125997 ≤ 464257069) S221C04.total S221C05.total

theorem join_0_3 : (twinPrimeSegment 464257069 464519213).card = 855 := by
  simpa using combineTwinPrimeSegments (by decide : 464257069 ≤ 464388141)
    (by decide : 464388141 ≤ 464519213) S221C06.total S221C07.total

theorem join_0_4 : (twinPrimeSegment 464519213 464781357).card = 861 := by
  simpa using combineTwinPrimeSegments (by decide : 464519213 ≤ 464650285)
    (by decide : 464650285 ≤ 464781357) S221C08.total S221C09.total

theorem join_0_5 : (twinPrimeSegment 464781357 465043501).card = 845 := by
  simpa using combineTwinPrimeSegments (by decide : 464781357 ≤ 464912429)
    (by decide : 464912429 ≤ 465043501) S221C10.total S221C11.total

theorem join_0_6 : (twinPrimeSegment 465043501 465305645).card = 866 := by
  simpa using combineTwinPrimeSegments (by decide : 465043501 ≤ 465174573)
    (by decide : 465174573 ≤ 465305645) S221C12.total S221C13.total

theorem join_0_7 : (twinPrimeSegment 465305645 465567789).card = 866 := by
  simpa using combineTwinPrimeSegments (by decide : 465305645 ≤ 465436717)
    (by decide : 465436717 ≤ 465567789) S221C14.total S221C15.total

theorem join_1_0 : (twinPrimeSegment 463470637 463994925).card = 1705 := by
  simpa using combineTwinPrimeSegments (by decide : 463470637 ≤ 463732781)
    (by decide : 463732781 ≤ 463994925) join_0_0 join_0_1

theorem join_1_1 : (twinPrimeSegment 463994925 464519213).card = 1711 := by
  simpa using combineTwinPrimeSegments (by decide : 463994925 ≤ 464257069)
    (by decide : 464257069 ≤ 464519213) join_0_2 join_0_3

theorem join_1_2 : (twinPrimeSegment 464519213 465043501).card = 1706 := by
  simpa using combineTwinPrimeSegments (by decide : 464519213 ≤ 464781357)
    (by decide : 464781357 ≤ 465043501) join_0_4 join_0_5

theorem join_1_3 : (twinPrimeSegment 465043501 465567789).card = 1732 := by
  simpa using combineTwinPrimeSegments (by decide : 465043501 ≤ 465305645)
    (by decide : 465305645 ≤ 465567789) join_0_6 join_0_7

theorem join_2_0 : (twinPrimeSegment 463470637 464519213).card = 3416 := by
  simpa using combineTwinPrimeSegments (by decide : 463470637 ≤ 463994925)
    (by decide : 463994925 ≤ 464519213) join_1_0 join_1_1

theorem join_2_1 : (twinPrimeSegment 464519213 465567789).card = 3438 := by
  simpa using combineTwinPrimeSegments (by decide : 464519213 ≤ 465043501)
    (by decide : 465043501 ≤ 465567789) join_1_2 join_1_3

theorem join_3_0 : (twinPrimeSegment 463470637 465567789).card = 6854 := by
  simpa using combineTwinPrimeSegments (by decide : 463470637 ≤ 464519213)
    (by decide : 464519213 ≤ 465567789) join_2_0 join_2_1

theorem total : (twinPrimeSegment 463470637 465567789).card = 6854 := join_3_0

end S221All
end Sude.GeneratedTwinScan
