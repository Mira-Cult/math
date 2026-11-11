import Sude.GeneratedTwinScan.S048C00
import Sude.GeneratedTwinScan.S048C01
import Sude.GeneratedTwinScan.S048C02
import Sude.GeneratedTwinScan.S048C03
import Sude.GeneratedTwinScan.S048C04
import Sude.GeneratedTwinScan.S048C05
import Sude.GeneratedTwinScan.S048C06
import Sude.GeneratedTwinScan.S048C07
import Sude.GeneratedTwinScan.S048C08
import Sude.GeneratedTwinScan.S048C09
import Sude.GeneratedTwinScan.S048C10
import Sude.GeneratedTwinScan.S048C11
import Sude.GeneratedTwinScan.S048C12
import Sude.GeneratedTwinScan.S048C13
import Sude.GeneratedTwinScan.S048C14
import Sude.GeneratedTwinScan.S048C15

/-! Combined FT source segment; Lean kernel check required. -/
namespace Sude.GeneratedTwinScan
namespace S048All

theorem join_0_0 : (twinPrimeSegment 100663341 100925485).card = 979 := by
  simpa using combineTwinPrimeSegments (by decide : 100663341 ≤ 100794413)
    (by decide : 100794413 ≤ 100925485) S048C00.total S048C01.total

theorem join_0_1 : (twinPrimeSegment 100925485 101187629).card = 1012 := by
  simpa using combineTwinPrimeSegments (by decide : 100925485 ≤ 101056557)
    (by decide : 101056557 ≤ 101187629) S048C02.total S048C03.total

theorem join_0_2 : (twinPrimeSegment 101187629 101449773).card = 994 := by
  simpa using combineTwinPrimeSegments (by decide : 101187629 ≤ 101318701)
    (by decide : 101318701 ≤ 101449773) S048C04.total S048C05.total

theorem join_0_3 : (twinPrimeSegment 101449773 101711917).card = 996 := by
  simpa using combineTwinPrimeSegments (by decide : 101449773 ≤ 101580845)
    (by decide : 101580845 ≤ 101711917) S048C06.total S048C07.total

theorem join_0_4 : (twinPrimeSegment 101711917 101974061).card = 1019 := by
  simpa using combineTwinPrimeSegments (by decide : 101711917 ≤ 101842989)
    (by decide : 101842989 ≤ 101974061) S048C08.total S048C09.total

theorem join_0_5 : (twinPrimeSegment 101974061 102236205).card = 1001 := by
  simpa using combineTwinPrimeSegments (by decide : 101974061 ≤ 102105133)
    (by decide : 102105133 ≤ 102236205) S048C10.total S048C11.total

theorem join_0_6 : (twinPrimeSegment 102236205 102498349).card = 1028 := by
  simpa using combineTwinPrimeSegments (by decide : 102236205 ≤ 102367277)
    (by decide : 102367277 ≤ 102498349) S048C12.total S048C13.total

theorem join_0_7 : (twinPrimeSegment 102498349 102760493).card = 1000 := by
  simpa using combineTwinPrimeSegments (by decide : 102498349 ≤ 102629421)
    (by decide : 102629421 ≤ 102760493) S048C14.total S048C15.total

theorem join_1_0 : (twinPrimeSegment 100663341 101187629).card = 1991 := by
  simpa using combineTwinPrimeSegments (by decide : 100663341 ≤ 100925485)
    (by decide : 100925485 ≤ 101187629) join_0_0 join_0_1

theorem join_1_1 : (twinPrimeSegment 101187629 101711917).card = 1990 := by
  simpa using combineTwinPrimeSegments (by decide : 101187629 ≤ 101449773)
    (by decide : 101449773 ≤ 101711917) join_0_2 join_0_3

theorem join_1_2 : (twinPrimeSegment 101711917 102236205).card = 2020 := by
  simpa using combineTwinPrimeSegments (by decide : 101711917 ≤ 101974061)
    (by decide : 101974061 ≤ 102236205) join_0_4 join_0_5

theorem join_1_3 : (twinPrimeSegment 102236205 102760493).card = 2028 := by
  simpa using combineTwinPrimeSegments (by decide : 102236205 ≤ 102498349)
    (by decide : 102498349 ≤ 102760493) join_0_6 join_0_7

theorem join_2_0 : (twinPrimeSegment 100663341 101711917).card = 3981 := by
  simpa using combineTwinPrimeSegments (by decide : 100663341 ≤ 101187629)
    (by decide : 101187629 ≤ 101711917) join_1_0 join_1_1

theorem join_2_1 : (twinPrimeSegment 101711917 102760493).card = 4048 := by
  simpa using combineTwinPrimeSegments (by decide : 101711917 ≤ 102236205)
    (by decide : 102236205 ≤ 102760493) join_1_2 join_1_3

theorem join_3_0 : (twinPrimeSegment 100663341 102760493).card = 8029 := by
  simpa using combineTwinPrimeSegments (by decide : 100663341 ≤ 101711917)
    (by decide : 101711917 ≤ 102760493) join_2_0 join_2_1

theorem total : (twinPrimeSegment 100663341 102760493).card = 8029 := join_3_0

end S048All
end Sude.GeneratedTwinScan
