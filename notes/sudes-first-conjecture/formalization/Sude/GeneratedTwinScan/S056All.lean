import Sude.GeneratedTwinScan.S056C00
import Sude.GeneratedTwinScan.S056C01
import Sude.GeneratedTwinScan.S056C02
import Sude.GeneratedTwinScan.S056C03
import Sude.GeneratedTwinScan.S056C04
import Sude.GeneratedTwinScan.S056C05
import Sude.GeneratedTwinScan.S056C06
import Sude.GeneratedTwinScan.S056C07
import Sude.GeneratedTwinScan.S056C08
import Sude.GeneratedTwinScan.S056C09
import Sude.GeneratedTwinScan.S056C10
import Sude.GeneratedTwinScan.S056C11
import Sude.GeneratedTwinScan.S056C12
import Sude.GeneratedTwinScan.S056C13
import Sude.GeneratedTwinScan.S056C14
import Sude.GeneratedTwinScan.S056C15

/-! Combined FT source segment; Lean kernel check required. -/
namespace Sude.GeneratedTwinScan
namespace S056All

theorem join_0_0 : (twinPrimeSegment 117440557 117702701).card = 1005 := by
  simpa using combineTwinPrimeSegments (by decide : 117440557 ≤ 117571629)
    (by decide : 117571629 ≤ 117702701) S056C00.total S056C01.total

theorem join_0_1 : (twinPrimeSegment 117702701 117964845).card = 978 := by
  simpa using combineTwinPrimeSegments (by decide : 117702701 ≤ 117833773)
    (by decide : 117833773 ≤ 117964845) S056C02.total S056C03.total

theorem join_0_2 : (twinPrimeSegment 117964845 118226989).card = 1028 := by
  simpa using combineTwinPrimeSegments (by decide : 117964845 ≤ 118095917)
    (by decide : 118095917 ≤ 118226989) S056C04.total S056C05.total

theorem join_0_3 : (twinPrimeSegment 118226989 118489133).card = 1013 := by
  simpa using combineTwinPrimeSegments (by decide : 118226989 ≤ 118358061)
    (by decide : 118358061 ≤ 118489133) S056C06.total S056C07.total

theorem join_0_4 : (twinPrimeSegment 118489133 118751277).card = 975 := by
  simpa using combineTwinPrimeSegments (by decide : 118489133 ≤ 118620205)
    (by decide : 118620205 ≤ 118751277) S056C08.total S056C09.total

theorem join_0_5 : (twinPrimeSegment 118751277 119013421).card = 995 := by
  simpa using combineTwinPrimeSegments (by decide : 118751277 ≤ 118882349)
    (by decide : 118882349 ≤ 119013421) S056C10.total S056C11.total

theorem join_0_6 : (twinPrimeSegment 119013421 119275565).card = 982 := by
  simpa using combineTwinPrimeSegments (by decide : 119013421 ≤ 119144493)
    (by decide : 119144493 ≤ 119275565) S056C12.total S056C13.total

theorem join_0_7 : (twinPrimeSegment 119275565 119537709).card = 985 := by
  simpa using combineTwinPrimeSegments (by decide : 119275565 ≤ 119406637)
    (by decide : 119406637 ≤ 119537709) S056C14.total S056C15.total

theorem join_1_0 : (twinPrimeSegment 117440557 117964845).card = 1983 := by
  simpa using combineTwinPrimeSegments (by decide : 117440557 ≤ 117702701)
    (by decide : 117702701 ≤ 117964845) join_0_0 join_0_1

theorem join_1_1 : (twinPrimeSegment 117964845 118489133).card = 2041 := by
  simpa using combineTwinPrimeSegments (by decide : 117964845 ≤ 118226989)
    (by decide : 118226989 ≤ 118489133) join_0_2 join_0_3

theorem join_1_2 : (twinPrimeSegment 118489133 119013421).card = 1970 := by
  simpa using combineTwinPrimeSegments (by decide : 118489133 ≤ 118751277)
    (by decide : 118751277 ≤ 119013421) join_0_4 join_0_5

theorem join_1_3 : (twinPrimeSegment 119013421 119537709).card = 1967 := by
  simpa using combineTwinPrimeSegments (by decide : 119013421 ≤ 119275565)
    (by decide : 119275565 ≤ 119537709) join_0_6 join_0_7

theorem join_2_0 : (twinPrimeSegment 117440557 118489133).card = 4024 := by
  simpa using combineTwinPrimeSegments (by decide : 117440557 ≤ 117964845)
    (by decide : 117964845 ≤ 118489133) join_1_0 join_1_1

theorem join_2_1 : (twinPrimeSegment 118489133 119537709).card = 3937 := by
  simpa using combineTwinPrimeSegments (by decide : 118489133 ≤ 119013421)
    (by decide : 119013421 ≤ 119537709) join_1_2 join_1_3

theorem join_3_0 : (twinPrimeSegment 117440557 119537709).card = 7961 := by
  simpa using combineTwinPrimeSegments (by decide : 117440557 ≤ 118489133)
    (by decide : 118489133 ≤ 119537709) join_2_0 join_2_1

theorem total : (twinPrimeSegment 117440557 119537709).card = 7961 := join_3_0

end S056All
end Sude.GeneratedTwinScan
