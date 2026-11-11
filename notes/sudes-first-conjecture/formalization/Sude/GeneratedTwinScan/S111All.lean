import Sude.GeneratedTwinScan.S111C00
import Sude.GeneratedTwinScan.S111C01
import Sude.GeneratedTwinScan.S111C02
import Sude.GeneratedTwinScan.S111C03
import Sude.GeneratedTwinScan.S111C04
import Sude.GeneratedTwinScan.S111C05
import Sude.GeneratedTwinScan.S111C06
import Sude.GeneratedTwinScan.S111C07
import Sude.GeneratedTwinScan.S111C08
import Sude.GeneratedTwinScan.S111C09
import Sude.GeneratedTwinScan.S111C10
import Sude.GeneratedTwinScan.S111C11
import Sude.GeneratedTwinScan.S111C12
import Sude.GeneratedTwinScan.S111C13
import Sude.GeneratedTwinScan.S111C14
import Sude.GeneratedTwinScan.S111C15

/-! Combined FT source segment; Lean kernel check required. -/
namespace Sude.GeneratedTwinScan
namespace S111All

theorem join_0_0 : (twinPrimeSegment 232783917 233046061).card = 898 := by
  simpa using combineTwinPrimeSegments (by decide : 232783917 ≤ 232914989)
    (by decide : 232914989 ≤ 233046061) S111C00.total S111C01.total

theorem join_0_1 : (twinPrimeSegment 233046061 233308205).card = 922 := by
  simpa using combineTwinPrimeSegments (by decide : 233046061 ≤ 233177133)
    (by decide : 233177133 ≤ 233308205) S111C02.total S111C03.total

theorem join_0_2 : (twinPrimeSegment 233308205 233570349).card = 934 := by
  simpa using combineTwinPrimeSegments (by decide : 233308205 ≤ 233439277)
    (by decide : 233439277 ≤ 233570349) S111C04.total S111C05.total

theorem join_0_3 : (twinPrimeSegment 233570349 233832493).card = 932 := by
  simpa using combineTwinPrimeSegments (by decide : 233570349 ≤ 233701421)
    (by decide : 233701421 ≤ 233832493) S111C06.total S111C07.total

theorem join_0_4 : (twinPrimeSegment 233832493 234094637).card = 915 := by
  simpa using combineTwinPrimeSegments (by decide : 233832493 ≤ 233963565)
    (by decide : 233963565 ≤ 234094637) S111C08.total S111C09.total

theorem join_0_5 : (twinPrimeSegment 234094637 234356781).card = 934 := by
  simpa using combineTwinPrimeSegments (by decide : 234094637 ≤ 234225709)
    (by decide : 234225709 ≤ 234356781) S111C10.total S111C11.total

theorem join_0_6 : (twinPrimeSegment 234356781 234618925).card = 916 := by
  simpa using combineTwinPrimeSegments (by decide : 234356781 ≤ 234487853)
    (by decide : 234487853 ≤ 234618925) S111C12.total S111C13.total

theorem join_0_7 : (twinPrimeSegment 234618925 234881069).card = 986 := by
  simpa using combineTwinPrimeSegments (by decide : 234618925 ≤ 234749997)
    (by decide : 234749997 ≤ 234881069) S111C14.total S111C15.total

theorem join_1_0 : (twinPrimeSegment 232783917 233308205).card = 1820 := by
  simpa using combineTwinPrimeSegments (by decide : 232783917 ≤ 233046061)
    (by decide : 233046061 ≤ 233308205) join_0_0 join_0_1

theorem join_1_1 : (twinPrimeSegment 233308205 233832493).card = 1866 := by
  simpa using combineTwinPrimeSegments (by decide : 233308205 ≤ 233570349)
    (by decide : 233570349 ≤ 233832493) join_0_2 join_0_3

theorem join_1_2 : (twinPrimeSegment 233832493 234356781).card = 1849 := by
  simpa using combineTwinPrimeSegments (by decide : 233832493 ≤ 234094637)
    (by decide : 234094637 ≤ 234356781) join_0_4 join_0_5

theorem join_1_3 : (twinPrimeSegment 234356781 234881069).card = 1902 := by
  simpa using combineTwinPrimeSegments (by decide : 234356781 ≤ 234618925)
    (by decide : 234618925 ≤ 234881069) join_0_6 join_0_7

theorem join_2_0 : (twinPrimeSegment 232783917 233832493).card = 3686 := by
  simpa using combineTwinPrimeSegments (by decide : 232783917 ≤ 233308205)
    (by decide : 233308205 ≤ 233832493) join_1_0 join_1_1

theorem join_2_1 : (twinPrimeSegment 233832493 234881069).card = 3751 := by
  simpa using combineTwinPrimeSegments (by decide : 233832493 ≤ 234356781)
    (by decide : 234356781 ≤ 234881069) join_1_2 join_1_3

theorem join_3_0 : (twinPrimeSegment 232783917 234881069).card = 7437 := by
  simpa using combineTwinPrimeSegments (by decide : 232783917 ≤ 233832493)
    (by decide : 233832493 ≤ 234881069) join_2_0 join_2_1

theorem total : (twinPrimeSegment 232783917 234881069).card = 7437 := join_3_0

end S111All
end Sude.GeneratedTwinScan
