import Sude.GeneratedTwinScan.S229C00
import Sude.GeneratedTwinScan.S229C01
import Sude.GeneratedTwinScan.S229C02
import Sude.GeneratedTwinScan.S229C03
import Sude.GeneratedTwinScan.S229C04
import Sude.GeneratedTwinScan.S229C05
import Sude.GeneratedTwinScan.S229C06
import Sude.GeneratedTwinScan.S229C07
import Sude.GeneratedTwinScan.S229C08
import Sude.GeneratedTwinScan.S229C09
import Sude.GeneratedTwinScan.S229C10
import Sude.GeneratedTwinScan.S229C11
import Sude.GeneratedTwinScan.S229C12
import Sude.GeneratedTwinScan.S229C13
import Sude.GeneratedTwinScan.S229C14
import Sude.GeneratedTwinScan.S229C15

/-! Combined FT source segment; Lean kernel check required. -/
namespace Sude.GeneratedTwinScan
namespace S229All

theorem join_0_0 : (twinPrimeSegment 480247853 480509997).card = 858 := by
  simpa using combineTwinPrimeSegments (by decide : 480247853 ≤ 480378925)
    (by decide : 480378925 ≤ 480509997) S229C00.total S229C01.total

theorem join_0_1 : (twinPrimeSegment 480509997 480772141).card = 840 := by
  simpa using combineTwinPrimeSegments (by decide : 480509997 ≤ 480641069)
    (by decide : 480641069 ≤ 480772141) S229C02.total S229C03.total

theorem join_0_2 : (twinPrimeSegment 480772141 481034285).card = 833 := by
  simpa using combineTwinPrimeSegments (by decide : 480772141 ≤ 480903213)
    (by decide : 480903213 ≤ 481034285) S229C04.total S229C05.total

theorem join_0_3 : (twinPrimeSegment 481034285 481296429).card = 839 := by
  simpa using combineTwinPrimeSegments (by decide : 481034285 ≤ 481165357)
    (by decide : 481165357 ≤ 481296429) S229C06.total S229C07.total

theorem join_0_4 : (twinPrimeSegment 481296429 481558573).card = 859 := by
  simpa using combineTwinPrimeSegments (by decide : 481296429 ≤ 481427501)
    (by decide : 481427501 ≤ 481558573) S229C08.total S229C09.total

theorem join_0_5 : (twinPrimeSegment 481558573 481820717).card = 869 := by
  simpa using combineTwinPrimeSegments (by decide : 481558573 ≤ 481689645)
    (by decide : 481689645 ≤ 481820717) S229C10.total S229C11.total

theorem join_0_6 : (twinPrimeSegment 481820717 482082861).card = 811 := by
  simpa using combineTwinPrimeSegments (by decide : 481820717 ≤ 481951789)
    (by decide : 481951789 ≤ 482082861) S229C12.total S229C13.total

theorem join_0_7 : (twinPrimeSegment 482082861 482345005).card = 900 := by
  simpa using combineTwinPrimeSegments (by decide : 482082861 ≤ 482213933)
    (by decide : 482213933 ≤ 482345005) S229C14.total S229C15.total

theorem join_1_0 : (twinPrimeSegment 480247853 480772141).card = 1698 := by
  simpa using combineTwinPrimeSegments (by decide : 480247853 ≤ 480509997)
    (by decide : 480509997 ≤ 480772141) join_0_0 join_0_1

theorem join_1_1 : (twinPrimeSegment 480772141 481296429).card = 1672 := by
  simpa using combineTwinPrimeSegments (by decide : 480772141 ≤ 481034285)
    (by decide : 481034285 ≤ 481296429) join_0_2 join_0_3

theorem join_1_2 : (twinPrimeSegment 481296429 481820717).card = 1728 := by
  simpa using combineTwinPrimeSegments (by decide : 481296429 ≤ 481558573)
    (by decide : 481558573 ≤ 481820717) join_0_4 join_0_5

theorem join_1_3 : (twinPrimeSegment 481820717 482345005).card = 1711 := by
  simpa using combineTwinPrimeSegments (by decide : 481820717 ≤ 482082861)
    (by decide : 482082861 ≤ 482345005) join_0_6 join_0_7

theorem join_2_0 : (twinPrimeSegment 480247853 481296429).card = 3370 := by
  simpa using combineTwinPrimeSegments (by decide : 480247853 ≤ 480772141)
    (by decide : 480772141 ≤ 481296429) join_1_0 join_1_1

theorem join_2_1 : (twinPrimeSegment 481296429 482345005).card = 3439 := by
  simpa using combineTwinPrimeSegments (by decide : 481296429 ≤ 481820717)
    (by decide : 481820717 ≤ 482345005) join_1_2 join_1_3

theorem join_3_0 : (twinPrimeSegment 480247853 482345005).card = 6809 := by
  simpa using combineTwinPrimeSegments (by decide : 480247853 ≤ 481296429)
    (by decide : 481296429 ≤ 482345005) join_2_0 join_2_1

theorem total : (twinPrimeSegment 480247853 482345005).card = 6809 := join_3_0

end S229All
end Sude.GeneratedTwinScan
