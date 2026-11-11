import Sude.GeneratedTwinScan.S142C00
import Sude.GeneratedTwinScan.S142C01
import Sude.GeneratedTwinScan.S142C02
import Sude.GeneratedTwinScan.S142C03
import Sude.GeneratedTwinScan.S142C04
import Sude.GeneratedTwinScan.S142C05
import Sude.GeneratedTwinScan.S142C06
import Sude.GeneratedTwinScan.S142C07
import Sude.GeneratedTwinScan.S142C08
import Sude.GeneratedTwinScan.S142C09
import Sude.GeneratedTwinScan.S142C10
import Sude.GeneratedTwinScan.S142C11
import Sude.GeneratedTwinScan.S142C12
import Sude.GeneratedTwinScan.S142C13
import Sude.GeneratedTwinScan.S142C14
import Sude.GeneratedTwinScan.S142C15

/-! Combined FT source segment; Lean kernel check required. -/
namespace Sude.GeneratedTwinScan
namespace S142All

theorem join_0_0 : (twinPrimeSegment 297795629 298057773).card = 920 := by
  simpa using combineTwinPrimeSegments (by decide : 297795629 ≤ 297926701)
    (by decide : 297926701 ≤ 298057773) S142C00.total S142C01.total

theorem join_0_1 : (twinPrimeSegment 298057773 298319917).card = 862 := by
  simpa using combineTwinPrimeSegments (by decide : 298057773 ≤ 298188845)
    (by decide : 298188845 ≤ 298319917) S142C02.total S142C03.total

theorem join_0_2 : (twinPrimeSegment 298319917 298582061).card = 932 := by
  simpa using combineTwinPrimeSegments (by decide : 298319917 ≤ 298450989)
    (by decide : 298450989 ≤ 298582061) S142C04.total S142C05.total

theorem join_0_3 : (twinPrimeSegment 298582061 298844205).card = 882 := by
  simpa using combineTwinPrimeSegments (by decide : 298582061 ≤ 298713133)
    (by decide : 298713133 ≤ 298844205) S142C06.total S142C07.total

theorem join_0_4 : (twinPrimeSegment 298844205 299106349).card = 924 := by
  simpa using combineTwinPrimeSegments (by decide : 298844205 ≤ 298975277)
    (by decide : 298975277 ≤ 299106349) S142C08.total S142C09.total

theorem join_0_5 : (twinPrimeSegment 299106349 299368493).card = 870 := by
  simpa using combineTwinPrimeSegments (by decide : 299106349 ≤ 299237421)
    (by decide : 299237421 ≤ 299368493) S142C10.total S142C11.total

theorem join_0_6 : (twinPrimeSegment 299368493 299630637).card = 945 := by
  simpa using combineTwinPrimeSegments (by decide : 299368493 ≤ 299499565)
    (by decide : 299499565 ≤ 299630637) S142C12.total S142C13.total

theorem join_0_7 : (twinPrimeSegment 299630637 299892781).card = 854 := by
  simpa using combineTwinPrimeSegments (by decide : 299630637 ≤ 299761709)
    (by decide : 299761709 ≤ 299892781) S142C14.total S142C15.total

theorem join_1_0 : (twinPrimeSegment 297795629 298319917).card = 1782 := by
  simpa using combineTwinPrimeSegments (by decide : 297795629 ≤ 298057773)
    (by decide : 298057773 ≤ 298319917) join_0_0 join_0_1

theorem join_1_1 : (twinPrimeSegment 298319917 298844205).card = 1814 := by
  simpa using combineTwinPrimeSegments (by decide : 298319917 ≤ 298582061)
    (by decide : 298582061 ≤ 298844205) join_0_2 join_0_3

theorem join_1_2 : (twinPrimeSegment 298844205 299368493).card = 1794 := by
  simpa using combineTwinPrimeSegments (by decide : 298844205 ≤ 299106349)
    (by decide : 299106349 ≤ 299368493) join_0_4 join_0_5

theorem join_1_3 : (twinPrimeSegment 299368493 299892781).card = 1799 := by
  simpa using combineTwinPrimeSegments (by decide : 299368493 ≤ 299630637)
    (by decide : 299630637 ≤ 299892781) join_0_6 join_0_7

theorem join_2_0 : (twinPrimeSegment 297795629 298844205).card = 3596 := by
  simpa using combineTwinPrimeSegments (by decide : 297795629 ≤ 298319917)
    (by decide : 298319917 ≤ 298844205) join_1_0 join_1_1

theorem join_2_1 : (twinPrimeSegment 298844205 299892781).card = 3593 := by
  simpa using combineTwinPrimeSegments (by decide : 298844205 ≤ 299368493)
    (by decide : 299368493 ≤ 299892781) join_1_2 join_1_3

theorem join_3_0 : (twinPrimeSegment 297795629 299892781).card = 7189 := by
  simpa using combineTwinPrimeSegments (by decide : 297795629 ≤ 298844205)
    (by decide : 298844205 ≤ 299892781) join_2_0 join_2_1

theorem total : (twinPrimeSegment 297795629 299892781).card = 7189 := join_3_0

end S142All
end Sude.GeneratedTwinScan
