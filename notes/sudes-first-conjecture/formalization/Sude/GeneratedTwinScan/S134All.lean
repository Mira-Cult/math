import Sude.GeneratedTwinScan.S134C00
import Sude.GeneratedTwinScan.S134C01
import Sude.GeneratedTwinScan.S134C02
import Sude.GeneratedTwinScan.S134C03
import Sude.GeneratedTwinScan.S134C04
import Sude.GeneratedTwinScan.S134C05
import Sude.GeneratedTwinScan.S134C06
import Sude.GeneratedTwinScan.S134C07
import Sude.GeneratedTwinScan.S134C08
import Sude.GeneratedTwinScan.S134C09
import Sude.GeneratedTwinScan.S134C10
import Sude.GeneratedTwinScan.S134C11
import Sude.GeneratedTwinScan.S134C12
import Sude.GeneratedTwinScan.S134C13
import Sude.GeneratedTwinScan.S134C14
import Sude.GeneratedTwinScan.S134C15

/-! Combined FT source segment; Lean kernel check required. -/
namespace Sude.GeneratedTwinScan
namespace S134All

theorem join_0_0 : (twinPrimeSegment 281018413 281280557).card = 926 := by
  simpa using combineTwinPrimeSegments (by decide : 281018413 ≤ 281149485)
    (by decide : 281149485 ≤ 281280557) S134C00.total S134C01.total

theorem join_0_1 : (twinPrimeSegment 281280557 281542701).card = 909 := by
  simpa using combineTwinPrimeSegments (by decide : 281280557 ≤ 281411629)
    (by decide : 281411629 ≤ 281542701) S134C02.total S134C03.total

theorem join_0_2 : (twinPrimeSegment 281542701 281804845).card = 939 := by
  simpa using combineTwinPrimeSegments (by decide : 281542701 ≤ 281673773)
    (by decide : 281673773 ≤ 281804845) S134C04.total S134C05.total

theorem join_0_3 : (twinPrimeSegment 281804845 282066989).card = 930 := by
  simpa using combineTwinPrimeSegments (by decide : 281804845 ≤ 281935917)
    (by decide : 281935917 ≤ 282066989) S134C06.total S134C07.total

theorem join_0_4 : (twinPrimeSegment 282066989 282329133).card = 893 := by
  simpa using combineTwinPrimeSegments (by decide : 282066989 ≤ 282198061)
    (by decide : 282198061 ≤ 282329133) S134C08.total S134C09.total

theorem join_0_5 : (twinPrimeSegment 282329133 282591277).card = 923 := by
  simpa using combineTwinPrimeSegments (by decide : 282329133 ≤ 282460205)
    (by decide : 282460205 ≤ 282591277) S134C10.total S134C11.total

theorem join_0_6 : (twinPrimeSegment 282591277 282853421).card = 908 := by
  simpa using combineTwinPrimeSegments (by decide : 282591277 ≤ 282722349)
    (by decide : 282722349 ≤ 282853421) S134C12.total S134C13.total

theorem join_0_7 : (twinPrimeSegment 282853421 283115565).card = 905 := by
  simpa using combineTwinPrimeSegments (by decide : 282853421 ≤ 282984493)
    (by decide : 282984493 ≤ 283115565) S134C14.total S134C15.total

theorem join_1_0 : (twinPrimeSegment 281018413 281542701).card = 1835 := by
  simpa using combineTwinPrimeSegments (by decide : 281018413 ≤ 281280557)
    (by decide : 281280557 ≤ 281542701) join_0_0 join_0_1

theorem join_1_1 : (twinPrimeSegment 281542701 282066989).card = 1869 := by
  simpa using combineTwinPrimeSegments (by decide : 281542701 ≤ 281804845)
    (by decide : 281804845 ≤ 282066989) join_0_2 join_0_3

theorem join_1_2 : (twinPrimeSegment 282066989 282591277).card = 1816 := by
  simpa using combineTwinPrimeSegments (by decide : 282066989 ≤ 282329133)
    (by decide : 282329133 ≤ 282591277) join_0_4 join_0_5

theorem join_1_3 : (twinPrimeSegment 282591277 283115565).card = 1813 := by
  simpa using combineTwinPrimeSegments (by decide : 282591277 ≤ 282853421)
    (by decide : 282853421 ≤ 283115565) join_0_6 join_0_7

theorem join_2_0 : (twinPrimeSegment 281018413 282066989).card = 3704 := by
  simpa using combineTwinPrimeSegments (by decide : 281018413 ≤ 281542701)
    (by decide : 281542701 ≤ 282066989) join_1_0 join_1_1

theorem join_2_1 : (twinPrimeSegment 282066989 283115565).card = 3629 := by
  simpa using combineTwinPrimeSegments (by decide : 282066989 ≤ 282591277)
    (by decide : 282591277 ≤ 283115565) join_1_2 join_1_3

theorem join_3_0 : (twinPrimeSegment 281018413 283115565).card = 7333 := by
  simpa using combineTwinPrimeSegments (by decide : 281018413 ≤ 282066989)
    (by decide : 282066989 ≤ 283115565) join_2_0 join_2_1

theorem total : (twinPrimeSegment 281018413 283115565).card = 7333 := join_3_0

end S134All
end Sude.GeneratedTwinScan
