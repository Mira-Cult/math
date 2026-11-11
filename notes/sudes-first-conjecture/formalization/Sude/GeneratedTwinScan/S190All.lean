import Sude.GeneratedTwinScan.S190C00
import Sude.GeneratedTwinScan.S190C01
import Sude.GeneratedTwinScan.S190C02
import Sude.GeneratedTwinScan.S190C03
import Sude.GeneratedTwinScan.S190C04
import Sude.GeneratedTwinScan.S190C05
import Sude.GeneratedTwinScan.S190C06
import Sude.GeneratedTwinScan.S190C07
import Sude.GeneratedTwinScan.S190C08
import Sude.GeneratedTwinScan.S190C09
import Sude.GeneratedTwinScan.S190C10
import Sude.GeneratedTwinScan.S190C11
import Sude.GeneratedTwinScan.S190C12
import Sude.GeneratedTwinScan.S190C13
import Sude.GeneratedTwinScan.S190C14
import Sude.GeneratedTwinScan.S190C15

/-! Combined FT source segment; Lean kernel check required. -/
namespace Sude.GeneratedTwinScan
namespace S190All

theorem join_0_0 : (twinPrimeSegment 398458925 398721069).card = 901 := by
  simpa using combineTwinPrimeSegments (by decide : 398458925 ≤ 398589997)
    (by decide : 398589997 ≤ 398721069) S190C00.total S190C01.total

theorem join_0_1 : (twinPrimeSegment 398721069 398983213).card = 867 := by
  simpa using combineTwinPrimeSegments (by decide : 398721069 ≤ 398852141)
    (by decide : 398852141 ≤ 398983213) S190C02.total S190C03.total

theorem join_0_2 : (twinPrimeSegment 398983213 399245357).card = 857 := by
  simpa using combineTwinPrimeSegments (by decide : 398983213 ≤ 399114285)
    (by decide : 399114285 ≤ 399245357) S190C04.total S190C05.total

theorem join_0_3 : (twinPrimeSegment 399245357 399507501).card = 886 := by
  simpa using combineTwinPrimeSegments (by decide : 399245357 ≤ 399376429)
    (by decide : 399376429 ≤ 399507501) S190C06.total S190C07.total

theorem join_0_4 : (twinPrimeSegment 399507501 399769645).card = 881 := by
  simpa using combineTwinPrimeSegments (by decide : 399507501 ≤ 399638573)
    (by decide : 399638573 ≤ 399769645) S190C08.total S190C09.total

theorem join_0_5 : (twinPrimeSegment 399769645 400031789).card = 878 := by
  simpa using combineTwinPrimeSegments (by decide : 399769645 ≤ 399900717)
    (by decide : 399900717 ≤ 400031789) S190C10.total S190C11.total

theorem join_0_6 : (twinPrimeSegment 400031789 400293933).card = 866 := by
  simpa using combineTwinPrimeSegments (by decide : 400031789 ≤ 400162861)
    (by decide : 400162861 ≤ 400293933) S190C12.total S190C13.total

theorem join_0_7 : (twinPrimeSegment 400293933 400556077).card = 879 := by
  simpa using combineTwinPrimeSegments (by decide : 400293933 ≤ 400425005)
    (by decide : 400425005 ≤ 400556077) S190C14.total S190C15.total

theorem join_1_0 : (twinPrimeSegment 398458925 398983213).card = 1768 := by
  simpa using combineTwinPrimeSegments (by decide : 398458925 ≤ 398721069)
    (by decide : 398721069 ≤ 398983213) join_0_0 join_0_1

theorem join_1_1 : (twinPrimeSegment 398983213 399507501).card = 1743 := by
  simpa using combineTwinPrimeSegments (by decide : 398983213 ≤ 399245357)
    (by decide : 399245357 ≤ 399507501) join_0_2 join_0_3

theorem join_1_2 : (twinPrimeSegment 399507501 400031789).card = 1759 := by
  simpa using combineTwinPrimeSegments (by decide : 399507501 ≤ 399769645)
    (by decide : 399769645 ≤ 400031789) join_0_4 join_0_5

theorem join_1_3 : (twinPrimeSegment 400031789 400556077).card = 1745 := by
  simpa using combineTwinPrimeSegments (by decide : 400031789 ≤ 400293933)
    (by decide : 400293933 ≤ 400556077) join_0_6 join_0_7

theorem join_2_0 : (twinPrimeSegment 398458925 399507501).card = 3511 := by
  simpa using combineTwinPrimeSegments (by decide : 398458925 ≤ 398983213)
    (by decide : 398983213 ≤ 399507501) join_1_0 join_1_1

theorem join_2_1 : (twinPrimeSegment 399507501 400556077).card = 3504 := by
  simpa using combineTwinPrimeSegments (by decide : 399507501 ≤ 400031789)
    (by decide : 400031789 ≤ 400556077) join_1_2 join_1_3

theorem join_3_0 : (twinPrimeSegment 398458925 400556077).card = 7015 := by
  simpa using combineTwinPrimeSegments (by decide : 398458925 ≤ 399507501)
    (by decide : 399507501 ≤ 400556077) join_2_0 join_2_1

theorem total : (twinPrimeSegment 398458925 400556077).card = 7015 := join_3_0

end S190All
end Sude.GeneratedTwinScan
