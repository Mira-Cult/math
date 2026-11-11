import Sude.GeneratedTwinScan.S017C00
import Sude.GeneratedTwinScan.S017C01
import Sude.GeneratedTwinScan.S017C02
import Sude.GeneratedTwinScan.S017C03
import Sude.GeneratedTwinScan.S017C04
import Sude.GeneratedTwinScan.S017C05
import Sude.GeneratedTwinScan.S017C06
import Sude.GeneratedTwinScan.S017C07
import Sude.GeneratedTwinScan.S017C08
import Sude.GeneratedTwinScan.S017C09
import Sude.GeneratedTwinScan.S017C10
import Sude.GeneratedTwinScan.S017C11
import Sude.GeneratedTwinScan.S017C12
import Sude.GeneratedTwinScan.S017C13
import Sude.GeneratedTwinScan.S017C14
import Sude.GeneratedTwinScan.S017C15

/-! Combined FT source segment; Lean kernel check required. -/
namespace Sude.GeneratedTwinScan
namespace S017All

theorem join_0_0 : (twinPrimeSegment 35651629 35913773).card = 1161 := by
  simpa using combineTwinPrimeSegments (by decide : 35651629 ≤ 35782701)
    (by decide : 35782701 ≤ 35913773) S017C00.total S017C01.total

theorem join_0_1 : (twinPrimeSegment 35913773 36175917).card = 1142 := by
  simpa using combineTwinPrimeSegments (by decide : 35913773 ≤ 36044845)
    (by decide : 36044845 ≤ 36175917) S017C02.total S017C03.total

theorem join_0_2 : (twinPrimeSegment 36175917 36438061).card = 1178 := by
  simpa using combineTwinPrimeSegments (by decide : 36175917 ≤ 36306989)
    (by decide : 36306989 ≤ 36438061) S017C04.total S017C05.total

theorem join_0_3 : (twinPrimeSegment 36438061 36700205).card = 1182 := by
  simpa using combineTwinPrimeSegments (by decide : 36438061 ≤ 36569133)
    (by decide : 36569133 ≤ 36700205) S017C06.total S017C07.total

theorem join_0_4 : (twinPrimeSegment 36700205 36962349).card = 1139 := by
  simpa using combineTwinPrimeSegments (by decide : 36700205 ≤ 36831277)
    (by decide : 36831277 ≤ 36962349) S017C08.total S017C09.total

theorem join_0_5 : (twinPrimeSegment 36962349 37224493).card = 1183 := by
  simpa using combineTwinPrimeSegments (by decide : 36962349 ≤ 37093421)
    (by decide : 37093421 ≤ 37224493) S017C10.total S017C11.total

theorem join_0_6 : (twinPrimeSegment 37224493 37486637).card = 1146 := by
  simpa using combineTwinPrimeSegments (by decide : 37224493 ≤ 37355565)
    (by decide : 37355565 ≤ 37486637) S017C12.total S017C13.total

theorem join_0_7 : (twinPrimeSegment 37486637 37748781).card = 1121 := by
  simpa using combineTwinPrimeSegments (by decide : 37486637 ≤ 37617709)
    (by decide : 37617709 ≤ 37748781) S017C14.total S017C15.total

theorem join_1_0 : (twinPrimeSegment 35651629 36175917).card = 2303 := by
  simpa using combineTwinPrimeSegments (by decide : 35651629 ≤ 35913773)
    (by decide : 35913773 ≤ 36175917) join_0_0 join_0_1

theorem join_1_1 : (twinPrimeSegment 36175917 36700205).card = 2360 := by
  simpa using combineTwinPrimeSegments (by decide : 36175917 ≤ 36438061)
    (by decide : 36438061 ≤ 36700205) join_0_2 join_0_3

theorem join_1_2 : (twinPrimeSegment 36700205 37224493).card = 2322 := by
  simpa using combineTwinPrimeSegments (by decide : 36700205 ≤ 36962349)
    (by decide : 36962349 ≤ 37224493) join_0_4 join_0_5

theorem join_1_3 : (twinPrimeSegment 37224493 37748781).card = 2267 := by
  simpa using combineTwinPrimeSegments (by decide : 37224493 ≤ 37486637)
    (by decide : 37486637 ≤ 37748781) join_0_6 join_0_7

theorem join_2_0 : (twinPrimeSegment 35651629 36700205).card = 4663 := by
  simpa using combineTwinPrimeSegments (by decide : 35651629 ≤ 36175917)
    (by decide : 36175917 ≤ 36700205) join_1_0 join_1_1

theorem join_2_1 : (twinPrimeSegment 36700205 37748781).card = 4589 := by
  simpa using combineTwinPrimeSegments (by decide : 36700205 ≤ 37224493)
    (by decide : 37224493 ≤ 37748781) join_1_2 join_1_3

theorem join_3_0 : (twinPrimeSegment 35651629 37748781).card = 9252 := by
  simpa using combineTwinPrimeSegments (by decide : 35651629 ≤ 36700205)
    (by decide : 36700205 ≤ 37748781) join_2_0 join_2_1

theorem total : (twinPrimeSegment 35651629 37748781).card = 9252 := join_3_0

end S017All
end Sude.GeneratedTwinScan
