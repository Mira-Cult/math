import Sude.GeneratedTwinScan.S189C00
import Sude.GeneratedTwinScan.S189C01
import Sude.GeneratedTwinScan.S189C02
import Sude.GeneratedTwinScan.S189C03
import Sude.GeneratedTwinScan.S189C04
import Sude.GeneratedTwinScan.S189C05
import Sude.GeneratedTwinScan.S189C06
import Sude.GeneratedTwinScan.S189C07
import Sude.GeneratedTwinScan.S189C08
import Sude.GeneratedTwinScan.S189C09
import Sude.GeneratedTwinScan.S189C10
import Sude.GeneratedTwinScan.S189C11
import Sude.GeneratedTwinScan.S189C12
import Sude.GeneratedTwinScan.S189C13
import Sude.GeneratedTwinScan.S189C14
import Sude.GeneratedTwinScan.S189C15

/-! Combined FT source segment; Lean kernel check required. -/
namespace Sude.GeneratedTwinScan
namespace S189All

theorem join_0_0 : (twinPrimeSegment 396361773 396623917).card = 917 := by
  simpa using combineTwinPrimeSegments (by decide : 396361773 ≤ 396492845)
    (by decide : 396492845 ≤ 396623917) S189C00.total S189C01.total

theorem join_0_1 : (twinPrimeSegment 396623917 396886061).card = 864 := by
  simpa using combineTwinPrimeSegments (by decide : 396623917 ≤ 396754989)
    (by decide : 396754989 ≤ 396886061) S189C02.total S189C03.total

theorem join_0_2 : (twinPrimeSegment 396886061 397148205).card = 889 := by
  simpa using combineTwinPrimeSegments (by decide : 396886061 ≤ 397017133)
    (by decide : 397017133 ≤ 397148205) S189C04.total S189C05.total

theorem join_0_3 : (twinPrimeSegment 397148205 397410349).card = 893 := by
  simpa using combineTwinPrimeSegments (by decide : 397148205 ≤ 397279277)
    (by decide : 397279277 ≤ 397410349) S189C06.total S189C07.total

theorem join_0_4 : (twinPrimeSegment 397410349 397672493).card = 879 := by
  simpa using combineTwinPrimeSegments (by decide : 397410349 ≤ 397541421)
    (by decide : 397541421 ≤ 397672493) S189C08.total S189C09.total

theorem join_0_5 : (twinPrimeSegment 397672493 397934637).card = 912 := by
  simpa using combineTwinPrimeSegments (by decide : 397672493 ≤ 397803565)
    (by decide : 397803565 ≤ 397934637) S189C10.total S189C11.total

theorem join_0_6 : (twinPrimeSegment 397934637 398196781).card = 846 := by
  simpa using combineTwinPrimeSegments (by decide : 397934637 ≤ 398065709)
    (by decide : 398065709 ≤ 398196781) S189C12.total S189C13.total

theorem join_0_7 : (twinPrimeSegment 398196781 398458925).card = 881 := by
  simpa using combineTwinPrimeSegments (by decide : 398196781 ≤ 398327853)
    (by decide : 398327853 ≤ 398458925) S189C14.total S189C15.total

theorem join_1_0 : (twinPrimeSegment 396361773 396886061).card = 1781 := by
  simpa using combineTwinPrimeSegments (by decide : 396361773 ≤ 396623917)
    (by decide : 396623917 ≤ 396886061) join_0_0 join_0_1

theorem join_1_1 : (twinPrimeSegment 396886061 397410349).card = 1782 := by
  simpa using combineTwinPrimeSegments (by decide : 396886061 ≤ 397148205)
    (by decide : 397148205 ≤ 397410349) join_0_2 join_0_3

theorem join_1_2 : (twinPrimeSegment 397410349 397934637).card = 1791 := by
  simpa using combineTwinPrimeSegments (by decide : 397410349 ≤ 397672493)
    (by decide : 397672493 ≤ 397934637) join_0_4 join_0_5

theorem join_1_3 : (twinPrimeSegment 397934637 398458925).card = 1727 := by
  simpa using combineTwinPrimeSegments (by decide : 397934637 ≤ 398196781)
    (by decide : 398196781 ≤ 398458925) join_0_6 join_0_7

theorem join_2_0 : (twinPrimeSegment 396361773 397410349).card = 3563 := by
  simpa using combineTwinPrimeSegments (by decide : 396361773 ≤ 396886061)
    (by decide : 396886061 ≤ 397410349) join_1_0 join_1_1

theorem join_2_1 : (twinPrimeSegment 397410349 398458925).card = 3518 := by
  simpa using combineTwinPrimeSegments (by decide : 397410349 ≤ 397934637)
    (by decide : 397934637 ≤ 398458925) join_1_2 join_1_3

theorem join_3_0 : (twinPrimeSegment 396361773 398458925).card = 7081 := by
  simpa using combineTwinPrimeSegments (by decide : 396361773 ≤ 397410349)
    (by decide : 397410349 ≤ 398458925) join_2_0 join_2_1

theorem total : (twinPrimeSegment 396361773 398458925).card = 7081 := join_3_0

end S189All
end Sude.GeneratedTwinScan
