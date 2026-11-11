import Sude.GeneratedTwinScan.S143C00
import Sude.GeneratedTwinScan.S143C01
import Sude.GeneratedTwinScan.S143C02
import Sude.GeneratedTwinScan.S143C03
import Sude.GeneratedTwinScan.S143C04
import Sude.GeneratedTwinScan.S143C05
import Sude.GeneratedTwinScan.S143C06
import Sude.GeneratedTwinScan.S143C07
import Sude.GeneratedTwinScan.S143C08
import Sude.GeneratedTwinScan.S143C09
import Sude.GeneratedTwinScan.S143C10
import Sude.GeneratedTwinScan.S143C11
import Sude.GeneratedTwinScan.S143C12
import Sude.GeneratedTwinScan.S143C13
import Sude.GeneratedTwinScan.S143C14
import Sude.GeneratedTwinScan.S143C15

/-! Combined FT source segment; Lean kernel check required. -/
namespace Sude.GeneratedTwinScan
namespace S143All

theorem join_0_0 : (twinPrimeSegment 299892781 300154925).card = 879 := by
  simpa using combineTwinPrimeSegments (by decide : 299892781 ≤ 300023853)
    (by decide : 300023853 ≤ 300154925) S143C00.total S143C01.total

theorem join_0_1 : (twinPrimeSegment 300154925 300417069).card = 948 := by
  simpa using combineTwinPrimeSegments (by decide : 300154925 ≤ 300285997)
    (by decide : 300285997 ≤ 300417069) S143C02.total S143C03.total

theorem join_0_2 : (twinPrimeSegment 300417069 300679213).card = 907 := by
  simpa using combineTwinPrimeSegments (by decide : 300417069 ≤ 300548141)
    (by decide : 300548141 ≤ 300679213) S143C04.total S143C05.total

theorem join_0_3 : (twinPrimeSegment 300679213 300941357).card = 930 := by
  simpa using combineTwinPrimeSegments (by decide : 300679213 ≤ 300810285)
    (by decide : 300810285 ≤ 300941357) S143C06.total S143C07.total

theorem join_0_4 : (twinPrimeSegment 300941357 301203501).card = 880 := by
  simpa using combineTwinPrimeSegments (by decide : 300941357 ≤ 301072429)
    (by decide : 301072429 ≤ 301203501) S143C08.total S143C09.total

theorem join_0_5 : (twinPrimeSegment 301203501 301465645).card = 920 := by
  simpa using combineTwinPrimeSegments (by decide : 301203501 ≤ 301334573)
    (by decide : 301334573 ≤ 301465645) S143C10.total S143C11.total

theorem join_0_6 : (twinPrimeSegment 301465645 301727789).card = 876 := by
  simpa using combineTwinPrimeSegments (by decide : 301465645 ≤ 301596717)
    (by decide : 301596717 ≤ 301727789) S143C12.total S143C13.total

theorem join_0_7 : (twinPrimeSegment 301727789 301989933).card = 886 := by
  simpa using combineTwinPrimeSegments (by decide : 301727789 ≤ 301858861)
    (by decide : 301858861 ≤ 301989933) S143C14.total S143C15.total

theorem join_1_0 : (twinPrimeSegment 299892781 300417069).card = 1827 := by
  simpa using combineTwinPrimeSegments (by decide : 299892781 ≤ 300154925)
    (by decide : 300154925 ≤ 300417069) join_0_0 join_0_1

theorem join_1_1 : (twinPrimeSegment 300417069 300941357).card = 1837 := by
  simpa using combineTwinPrimeSegments (by decide : 300417069 ≤ 300679213)
    (by decide : 300679213 ≤ 300941357) join_0_2 join_0_3

theorem join_1_2 : (twinPrimeSegment 300941357 301465645).card = 1800 := by
  simpa using combineTwinPrimeSegments (by decide : 300941357 ≤ 301203501)
    (by decide : 301203501 ≤ 301465645) join_0_4 join_0_5

theorem join_1_3 : (twinPrimeSegment 301465645 301989933).card = 1762 := by
  simpa using combineTwinPrimeSegments (by decide : 301465645 ≤ 301727789)
    (by decide : 301727789 ≤ 301989933) join_0_6 join_0_7

theorem join_2_0 : (twinPrimeSegment 299892781 300941357).card = 3664 := by
  simpa using combineTwinPrimeSegments (by decide : 299892781 ≤ 300417069)
    (by decide : 300417069 ≤ 300941357) join_1_0 join_1_1

theorem join_2_1 : (twinPrimeSegment 300941357 301989933).card = 3562 := by
  simpa using combineTwinPrimeSegments (by decide : 300941357 ≤ 301465645)
    (by decide : 301465645 ≤ 301989933) join_1_2 join_1_3

theorem join_3_0 : (twinPrimeSegment 299892781 301989933).card = 7226 := by
  simpa using combineTwinPrimeSegments (by decide : 299892781 ≤ 300941357)
    (by decide : 300941357 ≤ 301989933) join_2_0 join_2_1

theorem total : (twinPrimeSegment 299892781 301989933).card = 7226 := join_3_0

end S143All
end Sude.GeneratedTwinScan
