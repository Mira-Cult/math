import Sude.GeneratedTwinScan.S109C00
import Sude.GeneratedTwinScan.S109C01
import Sude.GeneratedTwinScan.S109C02
import Sude.GeneratedTwinScan.S109C03
import Sude.GeneratedTwinScan.S109C04
import Sude.GeneratedTwinScan.S109C05
import Sude.GeneratedTwinScan.S109C06
import Sude.GeneratedTwinScan.S109C07
import Sude.GeneratedTwinScan.S109C08
import Sude.GeneratedTwinScan.S109C09
import Sude.GeneratedTwinScan.S109C10
import Sude.GeneratedTwinScan.S109C11
import Sude.GeneratedTwinScan.S109C12
import Sude.GeneratedTwinScan.S109C13
import Sude.GeneratedTwinScan.S109C14
import Sude.GeneratedTwinScan.S109C15

/-! Combined FT source segment; Lean kernel check required. -/
namespace Sude.GeneratedTwinScan
namespace S109All

theorem join_0_0 : (twinPrimeSegment 228589613 228851757).card = 933 := by
  simpa using combineTwinPrimeSegments (by decide : 228589613 ≤ 228720685)
    (by decide : 228720685 ≤ 228851757) S109C00.total S109C01.total

theorem join_0_1 : (twinPrimeSegment 228851757 229113901).card = 899 := by
  simpa using combineTwinPrimeSegments (by decide : 228851757 ≤ 228982829)
    (by decide : 228982829 ≤ 229113901) S109C02.total S109C03.total

theorem join_0_2 : (twinPrimeSegment 229113901 229376045).card = 957 := by
  simpa using combineTwinPrimeSegments (by decide : 229113901 ≤ 229244973)
    (by decide : 229244973 ≤ 229376045) S109C04.total S109C05.total

theorem join_0_3 : (twinPrimeSegment 229376045 229638189).card = 953 := by
  simpa using combineTwinPrimeSegments (by decide : 229376045 ≤ 229507117)
    (by decide : 229507117 ≤ 229638189) S109C06.total S109C07.total

theorem join_0_4 : (twinPrimeSegment 229638189 229900333).card = 910 := by
  simpa using combineTwinPrimeSegments (by decide : 229638189 ≤ 229769261)
    (by decide : 229769261 ≤ 229900333) S109C08.total S109C09.total

theorem join_0_5 : (twinPrimeSegment 229900333 230162477).card = 913 := by
  simpa using combineTwinPrimeSegments (by decide : 229900333 ≤ 230031405)
    (by decide : 230031405 ≤ 230162477) S109C10.total S109C11.total

theorem join_0_6 : (twinPrimeSegment 230162477 230424621).card = 936 := by
  simpa using combineTwinPrimeSegments (by decide : 230162477 ≤ 230293549)
    (by decide : 230293549 ≤ 230424621) S109C12.total S109C13.total

theorem join_0_7 : (twinPrimeSegment 230424621 230686765).card = 944 := by
  simpa using combineTwinPrimeSegments (by decide : 230424621 ≤ 230555693)
    (by decide : 230555693 ≤ 230686765) S109C14.total S109C15.total

theorem join_1_0 : (twinPrimeSegment 228589613 229113901).card = 1832 := by
  simpa using combineTwinPrimeSegments (by decide : 228589613 ≤ 228851757)
    (by decide : 228851757 ≤ 229113901) join_0_0 join_0_1

theorem join_1_1 : (twinPrimeSegment 229113901 229638189).card = 1910 := by
  simpa using combineTwinPrimeSegments (by decide : 229113901 ≤ 229376045)
    (by decide : 229376045 ≤ 229638189) join_0_2 join_0_3

theorem join_1_2 : (twinPrimeSegment 229638189 230162477).card = 1823 := by
  simpa using combineTwinPrimeSegments (by decide : 229638189 ≤ 229900333)
    (by decide : 229900333 ≤ 230162477) join_0_4 join_0_5

theorem join_1_3 : (twinPrimeSegment 230162477 230686765).card = 1880 := by
  simpa using combineTwinPrimeSegments (by decide : 230162477 ≤ 230424621)
    (by decide : 230424621 ≤ 230686765) join_0_6 join_0_7

theorem join_2_0 : (twinPrimeSegment 228589613 229638189).card = 3742 := by
  simpa using combineTwinPrimeSegments (by decide : 228589613 ≤ 229113901)
    (by decide : 229113901 ≤ 229638189) join_1_0 join_1_1

theorem join_2_1 : (twinPrimeSegment 229638189 230686765).card = 3703 := by
  simpa using combineTwinPrimeSegments (by decide : 229638189 ≤ 230162477)
    (by decide : 230162477 ≤ 230686765) join_1_2 join_1_3

theorem join_3_0 : (twinPrimeSegment 228589613 230686765).card = 7445 := by
  simpa using combineTwinPrimeSegments (by decide : 228589613 ≤ 229638189)
    (by decide : 229638189 ≤ 230686765) join_2_0 join_2_1

theorem total : (twinPrimeSegment 228589613 230686765).card = 7445 := join_3_0

end S109All
end Sude.GeneratedTwinScan
