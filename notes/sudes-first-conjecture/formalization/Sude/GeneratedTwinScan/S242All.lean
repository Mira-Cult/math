import Sude.GeneratedTwinScan.S242C00
import Sude.GeneratedTwinScan.S242C01
import Sude.GeneratedTwinScan.S242C02
import Sude.GeneratedTwinScan.S242C03
import Sude.GeneratedTwinScan.S242C04
import Sude.GeneratedTwinScan.S242C05
import Sude.GeneratedTwinScan.S242C06
import Sude.GeneratedTwinScan.S242C07
import Sude.GeneratedTwinScan.S242C08
import Sude.GeneratedTwinScan.S242C09
import Sude.GeneratedTwinScan.S242C10
import Sude.GeneratedTwinScan.S242C11
import Sude.GeneratedTwinScan.S242C12
import Sude.GeneratedTwinScan.S242C13
import Sude.GeneratedTwinScan.S242C14
import Sude.GeneratedTwinScan.S242C15

/-! Combined FT source segment; Lean kernel check required. -/
namespace Sude.GeneratedTwinScan
namespace S242All

theorem join_0_0 : (twinPrimeSegment 507510829 507772973).card = 880 := by
  simpa using combineTwinPrimeSegments (by decide : 507510829 ≤ 507641901)
    (by decide : 507641901 ≤ 507772973) S242C00.total S242C01.total

theorem join_0_1 : (twinPrimeSegment 507772973 508035117).card = 872 := by
  simpa using combineTwinPrimeSegments (by decide : 507772973 ≤ 507904045)
    (by decide : 507904045 ≤ 508035117) S242C02.total S242C03.total

theorem join_0_2 : (twinPrimeSegment 508035117 508297261).card = 907 := by
  simpa using combineTwinPrimeSegments (by decide : 508035117 ≤ 508166189)
    (by decide : 508166189 ≤ 508297261) S242C04.total S242C05.total

theorem join_0_3 : (twinPrimeSegment 508297261 508559405).card = 898 := by
  simpa using combineTwinPrimeSegments (by decide : 508297261 ≤ 508428333)
    (by decide : 508428333 ≤ 508559405) S242C06.total S242C07.total

theorem join_0_4 : (twinPrimeSegment 508559405 508821549).card = 863 := by
  simpa using combineTwinPrimeSegments (by decide : 508559405 ≤ 508690477)
    (by decide : 508690477 ≤ 508821549) S242C08.total S242C09.total

theorem join_0_5 : (twinPrimeSegment 508821549 509083693).card = 847 := by
  simpa using combineTwinPrimeSegments (by decide : 508821549 ≤ 508952621)
    (by decide : 508952621 ≤ 509083693) S242C10.total S242C11.total

theorem join_0_6 : (twinPrimeSegment 509083693 509345837).card = 881 := by
  simpa using combineTwinPrimeSegments (by decide : 509083693 ≤ 509214765)
    (by decide : 509214765 ≤ 509345837) S242C12.total S242C13.total

theorem join_0_7 : (twinPrimeSegment 509345837 509607981).card = 860 := by
  simpa using combineTwinPrimeSegments (by decide : 509345837 ≤ 509476909)
    (by decide : 509476909 ≤ 509607981) S242C14.total S242C15.total

theorem join_1_0 : (twinPrimeSegment 507510829 508035117).card = 1752 := by
  simpa using combineTwinPrimeSegments (by decide : 507510829 ≤ 507772973)
    (by decide : 507772973 ≤ 508035117) join_0_0 join_0_1

theorem join_1_1 : (twinPrimeSegment 508035117 508559405).card = 1805 := by
  simpa using combineTwinPrimeSegments (by decide : 508035117 ≤ 508297261)
    (by decide : 508297261 ≤ 508559405) join_0_2 join_0_3

theorem join_1_2 : (twinPrimeSegment 508559405 509083693).card = 1710 := by
  simpa using combineTwinPrimeSegments (by decide : 508559405 ≤ 508821549)
    (by decide : 508821549 ≤ 509083693) join_0_4 join_0_5

theorem join_1_3 : (twinPrimeSegment 509083693 509607981).card = 1741 := by
  simpa using combineTwinPrimeSegments (by decide : 509083693 ≤ 509345837)
    (by decide : 509345837 ≤ 509607981) join_0_6 join_0_7

theorem join_2_0 : (twinPrimeSegment 507510829 508559405).card = 3557 := by
  simpa using combineTwinPrimeSegments (by decide : 507510829 ≤ 508035117)
    (by decide : 508035117 ≤ 508559405) join_1_0 join_1_1

theorem join_2_1 : (twinPrimeSegment 508559405 509607981).card = 3451 := by
  simpa using combineTwinPrimeSegments (by decide : 508559405 ≤ 509083693)
    (by decide : 509083693 ≤ 509607981) join_1_2 join_1_3

theorem join_3_0 : (twinPrimeSegment 507510829 509607981).card = 7008 := by
  simpa using combineTwinPrimeSegments (by decide : 507510829 ≤ 508559405)
    (by decide : 508559405 ≤ 509607981) join_2_0 join_2_1

theorem total : (twinPrimeSegment 507510829 509607981).card = 7008 := join_3_0

end S242All
end Sude.GeneratedTwinScan
