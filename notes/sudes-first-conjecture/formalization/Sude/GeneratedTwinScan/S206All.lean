import Sude.GeneratedTwinScan.S206C00
import Sude.GeneratedTwinScan.S206C01
import Sude.GeneratedTwinScan.S206C02
import Sude.GeneratedTwinScan.S206C03
import Sude.GeneratedTwinScan.S206C04
import Sude.GeneratedTwinScan.S206C05
import Sude.GeneratedTwinScan.S206C06
import Sude.GeneratedTwinScan.S206C07
import Sude.GeneratedTwinScan.S206C08
import Sude.GeneratedTwinScan.S206C09
import Sude.GeneratedTwinScan.S206C10
import Sude.GeneratedTwinScan.S206C11
import Sude.GeneratedTwinScan.S206C12
import Sude.GeneratedTwinScan.S206C13
import Sude.GeneratedTwinScan.S206C14
import Sude.GeneratedTwinScan.S206C15

/-! Combined FT source segment; Lean kernel check required. -/
namespace Sude.GeneratedTwinScan
namespace S206All

theorem join_0_0 : (twinPrimeSegment 432013357 432275501).card = 891 := by
  simpa using combineTwinPrimeSegments (by decide : 432013357 ≤ 432144429)
    (by decide : 432144429 ≤ 432275501) S206C00.total S206C01.total

theorem join_0_1 : (twinPrimeSegment 432275501 432537645).card = 845 := by
  simpa using combineTwinPrimeSegments (by decide : 432275501 ≤ 432406573)
    (by decide : 432406573 ≤ 432537645) S206C02.total S206C03.total

theorem join_0_2 : (twinPrimeSegment 432537645 432799789).card = 870 := by
  simpa using combineTwinPrimeSegments (by decide : 432537645 ≤ 432668717)
    (by decide : 432668717 ≤ 432799789) S206C04.total S206C05.total

theorem join_0_3 : (twinPrimeSegment 432799789 433061933).card = 861 := by
  simpa using combineTwinPrimeSegments (by decide : 432799789 ≤ 432930861)
    (by decide : 432930861 ≤ 433061933) S206C06.total S206C07.total

theorem join_0_4 : (twinPrimeSegment 433061933 433324077).card = 858 := by
  simpa using combineTwinPrimeSegments (by decide : 433061933 ≤ 433193005)
    (by decide : 433193005 ≤ 433324077) S206C08.total S206C09.total

theorem join_0_5 : (twinPrimeSegment 433324077 433586221).card = 876 := by
  simpa using combineTwinPrimeSegments (by decide : 433324077 ≤ 433455149)
    (by decide : 433455149 ≤ 433586221) S206C10.total S206C11.total

theorem join_0_6 : (twinPrimeSegment 433586221 433848365).card = 893 := by
  simpa using combineTwinPrimeSegments (by decide : 433586221 ≤ 433717293)
    (by decide : 433717293 ≤ 433848365) S206C12.total S206C13.total

theorem join_0_7 : (twinPrimeSegment 433848365 434110509).card = 913 := by
  simpa using combineTwinPrimeSegments (by decide : 433848365 ≤ 433979437)
    (by decide : 433979437 ≤ 434110509) S206C14.total S206C15.total

theorem join_1_0 : (twinPrimeSegment 432013357 432537645).card = 1736 := by
  simpa using combineTwinPrimeSegments (by decide : 432013357 ≤ 432275501)
    (by decide : 432275501 ≤ 432537645) join_0_0 join_0_1

theorem join_1_1 : (twinPrimeSegment 432537645 433061933).card = 1731 := by
  simpa using combineTwinPrimeSegments (by decide : 432537645 ≤ 432799789)
    (by decide : 432799789 ≤ 433061933) join_0_2 join_0_3

theorem join_1_2 : (twinPrimeSegment 433061933 433586221).card = 1734 := by
  simpa using combineTwinPrimeSegments (by decide : 433061933 ≤ 433324077)
    (by decide : 433324077 ≤ 433586221) join_0_4 join_0_5

theorem join_1_3 : (twinPrimeSegment 433586221 434110509).card = 1806 := by
  simpa using combineTwinPrimeSegments (by decide : 433586221 ≤ 433848365)
    (by decide : 433848365 ≤ 434110509) join_0_6 join_0_7

theorem join_2_0 : (twinPrimeSegment 432013357 433061933).card = 3467 := by
  simpa using combineTwinPrimeSegments (by decide : 432013357 ≤ 432537645)
    (by decide : 432537645 ≤ 433061933) join_1_0 join_1_1

theorem join_2_1 : (twinPrimeSegment 433061933 434110509).card = 3540 := by
  simpa using combineTwinPrimeSegments (by decide : 433061933 ≤ 433586221)
    (by decide : 433586221 ≤ 434110509) join_1_2 join_1_3

theorem join_3_0 : (twinPrimeSegment 432013357 434110509).card = 7007 := by
  simpa using combineTwinPrimeSegments (by decide : 432013357 ≤ 433061933)
    (by decide : 433061933 ≤ 434110509) join_2_0 join_2_1

theorem total : (twinPrimeSegment 432013357 434110509).card = 7007 := join_3_0

end S206All
end Sude.GeneratedTwinScan
