import Sude.GeneratedTwinScan.S079C00
import Sude.GeneratedTwinScan.S079C01
import Sude.GeneratedTwinScan.S079C02
import Sude.GeneratedTwinScan.S079C03
import Sude.GeneratedTwinScan.S079C04
import Sude.GeneratedTwinScan.S079C05
import Sude.GeneratedTwinScan.S079C06
import Sude.GeneratedTwinScan.S079C07
import Sude.GeneratedTwinScan.S079C08
import Sude.GeneratedTwinScan.S079C09
import Sude.GeneratedTwinScan.S079C10
import Sude.GeneratedTwinScan.S079C11
import Sude.GeneratedTwinScan.S079C12
import Sude.GeneratedTwinScan.S079C13
import Sude.GeneratedTwinScan.S079C14
import Sude.GeneratedTwinScan.S079C15

/-! Combined FT source segment; Lean kernel check required. -/
namespace Sude.GeneratedTwinScan
namespace S079All

theorem join_0_0 : (twinPrimeSegment 165675053 165937197).card = 979 := by
  simpa using combineTwinPrimeSegments (by decide : 165675053 ≤ 165806125)
    (by decide : 165806125 ≤ 165937197) S079C00.total S079C01.total

theorem join_0_1 : (twinPrimeSegment 165937197 166199341).card = 912 := by
  simpa using combineTwinPrimeSegments (by decide : 165937197 ≤ 166068269)
    (by decide : 166068269 ≤ 166199341) S079C02.total S079C03.total

theorem join_0_2 : (twinPrimeSegment 166199341 166461485).card = 1002 := by
  simpa using combineTwinPrimeSegments (by decide : 166199341 ≤ 166330413)
    (by decide : 166330413 ≤ 166461485) S079C04.total S079C05.total

theorem join_0_3 : (twinPrimeSegment 166461485 166723629).card = 976 := by
  simpa using combineTwinPrimeSegments (by decide : 166461485 ≤ 166592557)
    (by decide : 166592557 ≤ 166723629) S079C06.total S079C07.total

theorem join_0_4 : (twinPrimeSegment 166723629 166985773).card = 916 := by
  simpa using combineTwinPrimeSegments (by decide : 166723629 ≤ 166854701)
    (by decide : 166854701 ≤ 166985773) S079C08.total S079C09.total

theorem join_0_5 : (twinPrimeSegment 166985773 167247917).card = 1005 := by
  simpa using combineTwinPrimeSegments (by decide : 166985773 ≤ 167116845)
    (by decide : 167116845 ≤ 167247917) S079C10.total S079C11.total

theorem join_0_6 : (twinPrimeSegment 167247917 167510061).card = 957 := by
  simpa using combineTwinPrimeSegments (by decide : 167247917 ≤ 167378989)
    (by decide : 167378989 ≤ 167510061) S079C12.total S079C13.total

theorem join_0_7 : (twinPrimeSegment 167510061 167772205).card = 1001 := by
  simpa using combineTwinPrimeSegments (by decide : 167510061 ≤ 167641133)
    (by decide : 167641133 ≤ 167772205) S079C14.total S079C15.total

theorem join_1_0 : (twinPrimeSegment 165675053 166199341).card = 1891 := by
  simpa using combineTwinPrimeSegments (by decide : 165675053 ≤ 165937197)
    (by decide : 165937197 ≤ 166199341) join_0_0 join_0_1

theorem join_1_1 : (twinPrimeSegment 166199341 166723629).card = 1978 := by
  simpa using combineTwinPrimeSegments (by decide : 166199341 ≤ 166461485)
    (by decide : 166461485 ≤ 166723629) join_0_2 join_0_3

theorem join_1_2 : (twinPrimeSegment 166723629 167247917).card = 1921 := by
  simpa using combineTwinPrimeSegments (by decide : 166723629 ≤ 166985773)
    (by decide : 166985773 ≤ 167247917) join_0_4 join_0_5

theorem join_1_3 : (twinPrimeSegment 167247917 167772205).card = 1958 := by
  simpa using combineTwinPrimeSegments (by decide : 167247917 ≤ 167510061)
    (by decide : 167510061 ≤ 167772205) join_0_6 join_0_7

theorem join_2_0 : (twinPrimeSegment 165675053 166723629).card = 3869 := by
  simpa using combineTwinPrimeSegments (by decide : 165675053 ≤ 166199341)
    (by decide : 166199341 ≤ 166723629) join_1_0 join_1_1

theorem join_2_1 : (twinPrimeSegment 166723629 167772205).card = 3879 := by
  simpa using combineTwinPrimeSegments (by decide : 166723629 ≤ 167247917)
    (by decide : 167247917 ≤ 167772205) join_1_2 join_1_3

theorem join_3_0 : (twinPrimeSegment 165675053 167772205).card = 7748 := by
  simpa using combineTwinPrimeSegments (by decide : 165675053 ≤ 166723629)
    (by decide : 166723629 ≤ 167772205) join_2_0 join_2_1

theorem total : (twinPrimeSegment 165675053 167772205).card = 7748 := join_3_0

end S079All
end Sude.GeneratedTwinScan
