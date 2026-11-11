import Sude.GeneratedTwinScan.S204C00
import Sude.GeneratedTwinScan.S204C01
import Sude.GeneratedTwinScan.S204C02
import Sude.GeneratedTwinScan.S204C03
import Sude.GeneratedTwinScan.S204C04
import Sude.GeneratedTwinScan.S204C05
import Sude.GeneratedTwinScan.S204C06
import Sude.GeneratedTwinScan.S204C07
import Sude.GeneratedTwinScan.S204C08
import Sude.GeneratedTwinScan.S204C09
import Sude.GeneratedTwinScan.S204C10
import Sude.GeneratedTwinScan.S204C11
import Sude.GeneratedTwinScan.S204C12
import Sude.GeneratedTwinScan.S204C13
import Sude.GeneratedTwinScan.S204C14
import Sude.GeneratedTwinScan.S204C15

/-! Combined FT source segment; Lean kernel check required. -/
namespace Sude.GeneratedTwinScan
namespace S204All

theorem join_0_0 : (twinPrimeSegment 427819053 428081197).card = 861 := by
  simpa using combineTwinPrimeSegments (by decide : 427819053 ≤ 427950125)
    (by decide : 427950125 ≤ 428081197) S204C00.total S204C01.total

theorem join_0_1 : (twinPrimeSegment 428081197 428343341).card = 862 := by
  simpa using combineTwinPrimeSegments (by decide : 428081197 ≤ 428212269)
    (by decide : 428212269 ≤ 428343341) S204C02.total S204C03.total

theorem join_0_2 : (twinPrimeSegment 428343341 428605485).card = 846 := by
  simpa using combineTwinPrimeSegments (by decide : 428343341 ≤ 428474413)
    (by decide : 428474413 ≤ 428605485) S204C04.total S204C05.total

theorem join_0_3 : (twinPrimeSegment 428605485 428867629).card = 888 := by
  simpa using combineTwinPrimeSegments (by decide : 428605485 ≤ 428736557)
    (by decide : 428736557 ≤ 428867629) S204C06.total S204C07.total

theorem join_0_4 : (twinPrimeSegment 428867629 429129773).card = 851 := by
  simpa using combineTwinPrimeSegments (by decide : 428867629 ≤ 428998701)
    (by decide : 428998701 ≤ 429129773) S204C08.total S204C09.total

theorem join_0_5 : (twinPrimeSegment 429129773 429391917).card = 879 := by
  simpa using combineTwinPrimeSegments (by decide : 429129773 ≤ 429260845)
    (by decide : 429260845 ≤ 429391917) S204C10.total S204C11.total

theorem join_0_6 : (twinPrimeSegment 429391917 429654061).card = 884 := by
  simpa using combineTwinPrimeSegments (by decide : 429391917 ≤ 429522989)
    (by decide : 429522989 ≤ 429654061) S204C12.total S204C13.total

theorem join_0_7 : (twinPrimeSegment 429654061 429916205).card = 878 := by
  simpa using combineTwinPrimeSegments (by decide : 429654061 ≤ 429785133)
    (by decide : 429785133 ≤ 429916205) S204C14.total S204C15.total

theorem join_1_0 : (twinPrimeSegment 427819053 428343341).card = 1723 := by
  simpa using combineTwinPrimeSegments (by decide : 427819053 ≤ 428081197)
    (by decide : 428081197 ≤ 428343341) join_0_0 join_0_1

theorem join_1_1 : (twinPrimeSegment 428343341 428867629).card = 1734 := by
  simpa using combineTwinPrimeSegments (by decide : 428343341 ≤ 428605485)
    (by decide : 428605485 ≤ 428867629) join_0_2 join_0_3

theorem join_1_2 : (twinPrimeSegment 428867629 429391917).card = 1730 := by
  simpa using combineTwinPrimeSegments (by decide : 428867629 ≤ 429129773)
    (by decide : 429129773 ≤ 429391917) join_0_4 join_0_5

theorem join_1_3 : (twinPrimeSegment 429391917 429916205).card = 1762 := by
  simpa using combineTwinPrimeSegments (by decide : 429391917 ≤ 429654061)
    (by decide : 429654061 ≤ 429916205) join_0_6 join_0_7

theorem join_2_0 : (twinPrimeSegment 427819053 428867629).card = 3457 := by
  simpa using combineTwinPrimeSegments (by decide : 427819053 ≤ 428343341)
    (by decide : 428343341 ≤ 428867629) join_1_0 join_1_1

theorem join_2_1 : (twinPrimeSegment 428867629 429916205).card = 3492 := by
  simpa using combineTwinPrimeSegments (by decide : 428867629 ≤ 429391917)
    (by decide : 429391917 ≤ 429916205) join_1_2 join_1_3

theorem join_3_0 : (twinPrimeSegment 427819053 429916205).card = 6949 := by
  simpa using combineTwinPrimeSegments (by decide : 427819053 ≤ 428867629)
    (by decide : 428867629 ≤ 429916205) join_2_0 join_2_1

theorem total : (twinPrimeSegment 427819053 429916205).card = 6949 := join_3_0

end S204All
end Sude.GeneratedTwinScan
