import Sude.GeneratedTwinScan.S237C00
import Sude.GeneratedTwinScan.S237C01
import Sude.GeneratedTwinScan.S237C02
import Sude.GeneratedTwinScan.S237C03
import Sude.GeneratedTwinScan.S237C04
import Sude.GeneratedTwinScan.S237C05
import Sude.GeneratedTwinScan.S237C06
import Sude.GeneratedTwinScan.S237C07
import Sude.GeneratedTwinScan.S237C08
import Sude.GeneratedTwinScan.S237C09
import Sude.GeneratedTwinScan.S237C10
import Sude.GeneratedTwinScan.S237C11
import Sude.GeneratedTwinScan.S237C12
import Sude.GeneratedTwinScan.S237C13
import Sude.GeneratedTwinScan.S237C14
import Sude.GeneratedTwinScan.S237C15

/-! Combined FT source segment; Lean kernel check required. -/
namespace Sude.GeneratedTwinScan
namespace S237All

theorem join_0_0 : (twinPrimeSegment 497025069 497287213).card = 831 := by
  simpa using combineTwinPrimeSegments (by decide : 497025069 ≤ 497156141)
    (by decide : 497156141 ≤ 497287213) S237C00.total S237C01.total

theorem join_0_1 : (twinPrimeSegment 497287213 497549357).card = 873 := by
  simpa using combineTwinPrimeSegments (by decide : 497287213 ≤ 497418285)
    (by decide : 497418285 ≤ 497549357) S237C02.total S237C03.total

theorem join_0_2 : (twinPrimeSegment 497549357 497811501).card = 870 := by
  simpa using combineTwinPrimeSegments (by decide : 497549357 ≤ 497680429)
    (by decide : 497680429 ≤ 497811501) S237C04.total S237C05.total

theorem join_0_3 : (twinPrimeSegment 497811501 498073645).card = 889 := by
  simpa using combineTwinPrimeSegments (by decide : 497811501 ≤ 497942573)
    (by decide : 497942573 ≤ 498073645) S237C06.total S237C07.total

theorem join_0_4 : (twinPrimeSegment 498073645 498335789).card = 882 := by
  simpa using combineTwinPrimeSegments (by decide : 498073645 ≤ 498204717)
    (by decide : 498204717 ≤ 498335789) S237C08.total S237C09.total

theorem join_0_5 : (twinPrimeSegment 498335789 498597933).card = 862 := by
  simpa using combineTwinPrimeSegments (by decide : 498335789 ≤ 498466861)
    (by decide : 498466861 ≤ 498597933) S237C10.total S237C11.total

theorem join_0_6 : (twinPrimeSegment 498597933 498860077).card = 799 := by
  simpa using combineTwinPrimeSegments (by decide : 498597933 ≤ 498729005)
    (by decide : 498729005 ≤ 498860077) S237C12.total S237C13.total

theorem join_0_7 : (twinPrimeSegment 498860077 499122221).card = 874 := by
  simpa using combineTwinPrimeSegments (by decide : 498860077 ≤ 498991149)
    (by decide : 498991149 ≤ 499122221) S237C14.total S237C15.total

theorem join_1_0 : (twinPrimeSegment 497025069 497549357).card = 1704 := by
  simpa using combineTwinPrimeSegments (by decide : 497025069 ≤ 497287213)
    (by decide : 497287213 ≤ 497549357) join_0_0 join_0_1

theorem join_1_1 : (twinPrimeSegment 497549357 498073645).card = 1759 := by
  simpa using combineTwinPrimeSegments (by decide : 497549357 ≤ 497811501)
    (by decide : 497811501 ≤ 498073645) join_0_2 join_0_3

theorem join_1_2 : (twinPrimeSegment 498073645 498597933).card = 1744 := by
  simpa using combineTwinPrimeSegments (by decide : 498073645 ≤ 498335789)
    (by decide : 498335789 ≤ 498597933) join_0_4 join_0_5

theorem join_1_3 : (twinPrimeSegment 498597933 499122221).card = 1673 := by
  simpa using combineTwinPrimeSegments (by decide : 498597933 ≤ 498860077)
    (by decide : 498860077 ≤ 499122221) join_0_6 join_0_7

theorem join_2_0 : (twinPrimeSegment 497025069 498073645).card = 3463 := by
  simpa using combineTwinPrimeSegments (by decide : 497025069 ≤ 497549357)
    (by decide : 497549357 ≤ 498073645) join_1_0 join_1_1

theorem join_2_1 : (twinPrimeSegment 498073645 499122221).card = 3417 := by
  simpa using combineTwinPrimeSegments (by decide : 498073645 ≤ 498597933)
    (by decide : 498597933 ≤ 499122221) join_1_2 join_1_3

theorem join_3_0 : (twinPrimeSegment 497025069 499122221).card = 6880 := by
  simpa using combineTwinPrimeSegments (by decide : 497025069 ≤ 498073645)
    (by decide : 498073645 ≤ 499122221) join_2_0 join_2_1

theorem total : (twinPrimeSegment 497025069 499122221).card = 6880 := join_3_0

end S237All
end Sude.GeneratedTwinScan
