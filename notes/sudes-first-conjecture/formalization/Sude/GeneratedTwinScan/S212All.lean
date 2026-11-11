import Sude.GeneratedTwinScan.S212C00
import Sude.GeneratedTwinScan.S212C01
import Sude.GeneratedTwinScan.S212C02
import Sude.GeneratedTwinScan.S212C03
import Sude.GeneratedTwinScan.S212C04
import Sude.GeneratedTwinScan.S212C05
import Sude.GeneratedTwinScan.S212C06
import Sude.GeneratedTwinScan.S212C07
import Sude.GeneratedTwinScan.S212C08
import Sude.GeneratedTwinScan.S212C09
import Sude.GeneratedTwinScan.S212C10
import Sude.GeneratedTwinScan.S212C11
import Sude.GeneratedTwinScan.S212C12
import Sude.GeneratedTwinScan.S212C13
import Sude.GeneratedTwinScan.S212C14
import Sude.GeneratedTwinScan.S212C15

/-! Combined FT source segment; Lean kernel check required. -/
namespace Sude.GeneratedTwinScan
namespace S212All

theorem join_0_0 : (twinPrimeSegment 444596269 444858413).card = 904 := by
  simpa using combineTwinPrimeSegments (by decide : 444596269 ≤ 444727341)
    (by decide : 444727341 ≤ 444858413) S212C00.total S212C01.total

theorem join_0_1 : (twinPrimeSegment 444858413 445120557).card = 864 := by
  simpa using combineTwinPrimeSegments (by decide : 444858413 ≤ 444989485)
    (by decide : 444989485 ≤ 445120557) S212C02.total S212C03.total

theorem join_0_2 : (twinPrimeSegment 445120557 445382701).card = 861 := by
  simpa using combineTwinPrimeSegments (by decide : 445120557 ≤ 445251629)
    (by decide : 445251629 ≤ 445382701) S212C04.total S212C05.total

theorem join_0_3 : (twinPrimeSegment 445382701 445644845).card = 858 := by
  simpa using combineTwinPrimeSegments (by decide : 445382701 ≤ 445513773)
    (by decide : 445513773 ≤ 445644845) S212C06.total S212C07.total

theorem join_0_4 : (twinPrimeSegment 445644845 445906989).card = 876 := by
  simpa using combineTwinPrimeSegments (by decide : 445644845 ≤ 445775917)
    (by decide : 445775917 ≤ 445906989) S212C08.total S212C09.total

theorem join_0_5 : (twinPrimeSegment 445906989 446169133).card = 908 := by
  simpa using combineTwinPrimeSegments (by decide : 445906989 ≤ 446038061)
    (by decide : 446038061 ≤ 446169133) S212C10.total S212C11.total

theorem join_0_6 : (twinPrimeSegment 446169133 446431277).card = 878 := by
  simpa using combineTwinPrimeSegments (by decide : 446169133 ≤ 446300205)
    (by decide : 446300205 ≤ 446431277) S212C12.total S212C13.total

theorem join_0_7 : (twinPrimeSegment 446431277 446693421).card = 870 := by
  simpa using combineTwinPrimeSegments (by decide : 446431277 ≤ 446562349)
    (by decide : 446562349 ≤ 446693421) S212C14.total S212C15.total

theorem join_1_0 : (twinPrimeSegment 444596269 445120557).card = 1768 := by
  simpa using combineTwinPrimeSegments (by decide : 444596269 ≤ 444858413)
    (by decide : 444858413 ≤ 445120557) join_0_0 join_0_1

theorem join_1_1 : (twinPrimeSegment 445120557 445644845).card = 1719 := by
  simpa using combineTwinPrimeSegments (by decide : 445120557 ≤ 445382701)
    (by decide : 445382701 ≤ 445644845) join_0_2 join_0_3

theorem join_1_2 : (twinPrimeSegment 445644845 446169133).card = 1784 := by
  simpa using combineTwinPrimeSegments (by decide : 445644845 ≤ 445906989)
    (by decide : 445906989 ≤ 446169133) join_0_4 join_0_5

theorem join_1_3 : (twinPrimeSegment 446169133 446693421).card = 1748 := by
  simpa using combineTwinPrimeSegments (by decide : 446169133 ≤ 446431277)
    (by decide : 446431277 ≤ 446693421) join_0_6 join_0_7

theorem join_2_0 : (twinPrimeSegment 444596269 445644845).card = 3487 := by
  simpa using combineTwinPrimeSegments (by decide : 444596269 ≤ 445120557)
    (by decide : 445120557 ≤ 445644845) join_1_0 join_1_1

theorem join_2_1 : (twinPrimeSegment 445644845 446693421).card = 3532 := by
  simpa using combineTwinPrimeSegments (by decide : 445644845 ≤ 446169133)
    (by decide : 446169133 ≤ 446693421) join_1_2 join_1_3

theorem join_3_0 : (twinPrimeSegment 444596269 446693421).card = 7019 := by
  simpa using combineTwinPrimeSegments (by decide : 444596269 ≤ 445644845)
    (by decide : 445644845 ≤ 446693421) join_2_0 join_2_1

theorem total : (twinPrimeSegment 444596269 446693421).card = 7019 := join_3_0

end S212All
end Sude.GeneratedTwinScan
