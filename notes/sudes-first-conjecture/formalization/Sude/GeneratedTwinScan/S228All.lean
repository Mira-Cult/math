import Sude.GeneratedTwinScan.S228C00
import Sude.GeneratedTwinScan.S228C01
import Sude.GeneratedTwinScan.S228C02
import Sude.GeneratedTwinScan.S228C03
import Sude.GeneratedTwinScan.S228C04
import Sude.GeneratedTwinScan.S228C05
import Sude.GeneratedTwinScan.S228C06
import Sude.GeneratedTwinScan.S228C07
import Sude.GeneratedTwinScan.S228C08
import Sude.GeneratedTwinScan.S228C09
import Sude.GeneratedTwinScan.S228C10
import Sude.GeneratedTwinScan.S228C11
import Sude.GeneratedTwinScan.S228C12
import Sude.GeneratedTwinScan.S228C13
import Sude.GeneratedTwinScan.S228C14
import Sude.GeneratedTwinScan.S228C15

/-! Combined FT source segment; Lean kernel check required. -/
namespace Sude.GeneratedTwinScan
namespace S228All

theorem join_0_0 : (twinPrimeSegment 478150701 478412845).card = 878 := by
  simpa using combineTwinPrimeSegments (by decide : 478150701 ≤ 478281773)
    (by decide : 478281773 ≤ 478412845) S228C00.total S228C01.total

theorem join_0_1 : (twinPrimeSegment 478412845 478674989).card = 883 := by
  simpa using combineTwinPrimeSegments (by decide : 478412845 ≤ 478543917)
    (by decide : 478543917 ≤ 478674989) S228C02.total S228C03.total

theorem join_0_2 : (twinPrimeSegment 478674989 478937133).card = 892 := by
  simpa using combineTwinPrimeSegments (by decide : 478674989 ≤ 478806061)
    (by decide : 478806061 ≤ 478937133) S228C04.total S228C05.total

theorem join_0_3 : (twinPrimeSegment 478937133 479199277).card = 871 := by
  simpa using combineTwinPrimeSegments (by decide : 478937133 ≤ 479068205)
    (by decide : 479068205 ≤ 479199277) S228C06.total S228C07.total

theorem join_0_4 : (twinPrimeSegment 479199277 479461421).card = 871 := by
  simpa using combineTwinPrimeSegments (by decide : 479199277 ≤ 479330349)
    (by decide : 479330349 ≤ 479461421) S228C08.total S228C09.total

theorem join_0_5 : (twinPrimeSegment 479461421 479723565).card = 890 := by
  simpa using combineTwinPrimeSegments (by decide : 479461421 ≤ 479592493)
    (by decide : 479592493 ≤ 479723565) S228C10.total S228C11.total

theorem join_0_6 : (twinPrimeSegment 479723565 479985709).card = 849 := by
  simpa using combineTwinPrimeSegments (by decide : 479723565 ≤ 479854637)
    (by decide : 479854637 ≤ 479985709) S228C12.total S228C13.total

theorem join_0_7 : (twinPrimeSegment 479985709 480247853).card = 826 := by
  simpa using combineTwinPrimeSegments (by decide : 479985709 ≤ 480116781)
    (by decide : 480116781 ≤ 480247853) S228C14.total S228C15.total

theorem join_1_0 : (twinPrimeSegment 478150701 478674989).card = 1761 := by
  simpa using combineTwinPrimeSegments (by decide : 478150701 ≤ 478412845)
    (by decide : 478412845 ≤ 478674989) join_0_0 join_0_1

theorem join_1_1 : (twinPrimeSegment 478674989 479199277).card = 1763 := by
  simpa using combineTwinPrimeSegments (by decide : 478674989 ≤ 478937133)
    (by decide : 478937133 ≤ 479199277) join_0_2 join_0_3

theorem join_1_2 : (twinPrimeSegment 479199277 479723565).card = 1761 := by
  simpa using combineTwinPrimeSegments (by decide : 479199277 ≤ 479461421)
    (by decide : 479461421 ≤ 479723565) join_0_4 join_0_5

theorem join_1_3 : (twinPrimeSegment 479723565 480247853).card = 1675 := by
  simpa using combineTwinPrimeSegments (by decide : 479723565 ≤ 479985709)
    (by decide : 479985709 ≤ 480247853) join_0_6 join_0_7

theorem join_2_0 : (twinPrimeSegment 478150701 479199277).card = 3524 := by
  simpa using combineTwinPrimeSegments (by decide : 478150701 ≤ 478674989)
    (by decide : 478674989 ≤ 479199277) join_1_0 join_1_1

theorem join_2_1 : (twinPrimeSegment 479199277 480247853).card = 3436 := by
  simpa using combineTwinPrimeSegments (by decide : 479199277 ≤ 479723565)
    (by decide : 479723565 ≤ 480247853) join_1_2 join_1_3

theorem join_3_0 : (twinPrimeSegment 478150701 480247853).card = 6960 := by
  simpa using combineTwinPrimeSegments (by decide : 478150701 ≤ 479199277)
    (by decide : 479199277 ≤ 480247853) join_2_0 join_2_1

theorem total : (twinPrimeSegment 478150701 480247853).card = 6960 := join_3_0

end S228All
end Sude.GeneratedTwinScan
