import Sude.GeneratedTwinScan.S235C00
import Sude.GeneratedTwinScan.S235C01
import Sude.GeneratedTwinScan.S235C02
import Sude.GeneratedTwinScan.S235C03
import Sude.GeneratedTwinScan.S235C04
import Sude.GeneratedTwinScan.S235C05
import Sude.GeneratedTwinScan.S235C06
import Sude.GeneratedTwinScan.S235C07
import Sude.GeneratedTwinScan.S235C08
import Sude.GeneratedTwinScan.S235C09
import Sude.GeneratedTwinScan.S235C10
import Sude.GeneratedTwinScan.S235C11
import Sude.GeneratedTwinScan.S235C12
import Sude.GeneratedTwinScan.S235C13
import Sude.GeneratedTwinScan.S235C14
import Sude.GeneratedTwinScan.S235C15

/-! Combined FT source segment; Lean kernel check required. -/
namespace Sude.GeneratedTwinScan
namespace S235All

theorem join_0_0 : (twinPrimeSegment 492830765 493092909).card = 829 := by
  simpa using combineTwinPrimeSegments (by decide : 492830765 ≤ 492961837)
    (by decide : 492961837 ≤ 493092909) S235C00.total S235C01.total

theorem join_0_1 : (twinPrimeSegment 493092909 493355053).card = 871 := by
  simpa using combineTwinPrimeSegments (by decide : 493092909 ≤ 493223981)
    (by decide : 493223981 ≤ 493355053) S235C02.total S235C03.total

theorem join_0_2 : (twinPrimeSegment 493355053 493617197).card = 836 := by
  simpa using combineTwinPrimeSegments (by decide : 493355053 ≤ 493486125)
    (by decide : 493486125 ≤ 493617197) S235C04.total S235C05.total

theorem join_0_3 : (twinPrimeSegment 493617197 493879341).card = 833 := by
  simpa using combineTwinPrimeSegments (by decide : 493617197 ≤ 493748269)
    (by decide : 493748269 ≤ 493879341) S235C06.total S235C07.total

theorem join_0_4 : (twinPrimeSegment 493879341 494141485).card = 868 := by
  simpa using combineTwinPrimeSegments (by decide : 493879341 ≤ 494010413)
    (by decide : 494010413 ≤ 494141485) S235C08.total S235C09.total

theorem join_0_5 : (twinPrimeSegment 494141485 494403629).card = 879 := by
  simpa using combineTwinPrimeSegments (by decide : 494141485 ≤ 494272557)
    (by decide : 494272557 ≤ 494403629) S235C10.total S235C11.total

theorem join_0_6 : (twinPrimeSegment 494403629 494665773).card = 829 := by
  simpa using combineTwinPrimeSegments (by decide : 494403629 ≤ 494534701)
    (by decide : 494534701 ≤ 494665773) S235C12.total S235C13.total

theorem join_0_7 : (twinPrimeSegment 494665773 494927917).card = 893 := by
  simpa using combineTwinPrimeSegments (by decide : 494665773 ≤ 494796845)
    (by decide : 494796845 ≤ 494927917) S235C14.total S235C15.total

theorem join_1_0 : (twinPrimeSegment 492830765 493355053).card = 1700 := by
  simpa using combineTwinPrimeSegments (by decide : 492830765 ≤ 493092909)
    (by decide : 493092909 ≤ 493355053) join_0_0 join_0_1

theorem join_1_1 : (twinPrimeSegment 493355053 493879341).card = 1669 := by
  simpa using combineTwinPrimeSegments (by decide : 493355053 ≤ 493617197)
    (by decide : 493617197 ≤ 493879341) join_0_2 join_0_3

theorem join_1_2 : (twinPrimeSegment 493879341 494403629).card = 1747 := by
  simpa using combineTwinPrimeSegments (by decide : 493879341 ≤ 494141485)
    (by decide : 494141485 ≤ 494403629) join_0_4 join_0_5

theorem join_1_3 : (twinPrimeSegment 494403629 494927917).card = 1722 := by
  simpa using combineTwinPrimeSegments (by decide : 494403629 ≤ 494665773)
    (by decide : 494665773 ≤ 494927917) join_0_6 join_0_7

theorem join_2_0 : (twinPrimeSegment 492830765 493879341).card = 3369 := by
  simpa using combineTwinPrimeSegments (by decide : 492830765 ≤ 493355053)
    (by decide : 493355053 ≤ 493879341) join_1_0 join_1_1

theorem join_2_1 : (twinPrimeSegment 493879341 494927917).card = 3469 := by
  simpa using combineTwinPrimeSegments (by decide : 493879341 ≤ 494403629)
    (by decide : 494403629 ≤ 494927917) join_1_2 join_1_3

theorem join_3_0 : (twinPrimeSegment 492830765 494927917).card = 6838 := by
  simpa using combineTwinPrimeSegments (by decide : 492830765 ≤ 493879341)
    (by decide : 493879341 ≤ 494927917) join_2_0 join_2_1

theorem total : (twinPrimeSegment 492830765 494927917).card = 6838 := join_3_0

end S235All
end Sude.GeneratedTwinScan
