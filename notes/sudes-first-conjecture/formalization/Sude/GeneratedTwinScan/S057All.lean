import Sude.GeneratedTwinScan.S057C00
import Sude.GeneratedTwinScan.S057C01
import Sude.GeneratedTwinScan.S057C02
import Sude.GeneratedTwinScan.S057C03
import Sude.GeneratedTwinScan.S057C04
import Sude.GeneratedTwinScan.S057C05
import Sude.GeneratedTwinScan.S057C06
import Sude.GeneratedTwinScan.S057C07
import Sude.GeneratedTwinScan.S057C08
import Sude.GeneratedTwinScan.S057C09
import Sude.GeneratedTwinScan.S057C10
import Sude.GeneratedTwinScan.S057C11
import Sude.GeneratedTwinScan.S057C12
import Sude.GeneratedTwinScan.S057C13
import Sude.GeneratedTwinScan.S057C14
import Sude.GeneratedTwinScan.S057C15

/-! Combined FT source segment; Lean kernel check required. -/
namespace Sude.GeneratedTwinScan
namespace S057All

theorem join_0_0 : (twinPrimeSegment 119537709 119799853).card = 972 := by
  simpa using combineTwinPrimeSegments (by decide : 119537709 ≤ 119668781)
    (by decide : 119668781 ≤ 119799853) S057C00.total S057C01.total

theorem join_0_1 : (twinPrimeSegment 119799853 120061997).card = 989 := by
  simpa using combineTwinPrimeSegments (by decide : 119799853 ≤ 119930925)
    (by decide : 119930925 ≤ 120061997) S057C02.total S057C03.total

theorem join_0_2 : (twinPrimeSegment 120061997 120324141).card = 1006 := by
  simpa using combineTwinPrimeSegments (by decide : 120061997 ≤ 120193069)
    (by decide : 120193069 ≤ 120324141) S057C04.total S057C05.total

theorem join_0_3 : (twinPrimeSegment 120324141 120586285).card = 1013 := by
  simpa using combineTwinPrimeSegments (by decide : 120324141 ≤ 120455213)
    (by decide : 120455213 ≤ 120586285) S057C06.total S057C07.total

theorem join_0_4 : (twinPrimeSegment 120586285 120848429).card = 934 := by
  simpa using combineTwinPrimeSegments (by decide : 120586285 ≤ 120717357)
    (by decide : 120717357 ≤ 120848429) S057C08.total S057C09.total

theorem join_0_5 : (twinPrimeSegment 120848429 121110573).card = 974 := by
  simpa using combineTwinPrimeSegments (by decide : 120848429 ≤ 120979501)
    (by decide : 120979501 ≤ 121110573) S057C10.total S057C11.total

theorem join_0_6 : (twinPrimeSegment 121110573 121372717).card = 997 := by
  simpa using combineTwinPrimeSegments (by decide : 121110573 ≤ 121241645)
    (by decide : 121241645 ≤ 121372717) S057C12.total S057C13.total

theorem join_0_7 : (twinPrimeSegment 121372717 121634861).card = 1028 := by
  simpa using combineTwinPrimeSegments (by decide : 121372717 ≤ 121503789)
    (by decide : 121503789 ≤ 121634861) S057C14.total S057C15.total

theorem join_1_0 : (twinPrimeSegment 119537709 120061997).card = 1961 := by
  simpa using combineTwinPrimeSegments (by decide : 119537709 ≤ 119799853)
    (by decide : 119799853 ≤ 120061997) join_0_0 join_0_1

theorem join_1_1 : (twinPrimeSegment 120061997 120586285).card = 2019 := by
  simpa using combineTwinPrimeSegments (by decide : 120061997 ≤ 120324141)
    (by decide : 120324141 ≤ 120586285) join_0_2 join_0_3

theorem join_1_2 : (twinPrimeSegment 120586285 121110573).card = 1908 := by
  simpa using combineTwinPrimeSegments (by decide : 120586285 ≤ 120848429)
    (by decide : 120848429 ≤ 121110573) join_0_4 join_0_5

theorem join_1_3 : (twinPrimeSegment 121110573 121634861).card = 2025 := by
  simpa using combineTwinPrimeSegments (by decide : 121110573 ≤ 121372717)
    (by decide : 121372717 ≤ 121634861) join_0_6 join_0_7

theorem join_2_0 : (twinPrimeSegment 119537709 120586285).card = 3980 := by
  simpa using combineTwinPrimeSegments (by decide : 119537709 ≤ 120061997)
    (by decide : 120061997 ≤ 120586285) join_1_0 join_1_1

theorem join_2_1 : (twinPrimeSegment 120586285 121634861).card = 3933 := by
  simpa using combineTwinPrimeSegments (by decide : 120586285 ≤ 121110573)
    (by decide : 121110573 ≤ 121634861) join_1_2 join_1_3

theorem join_3_0 : (twinPrimeSegment 119537709 121634861).card = 7913 := by
  simpa using combineTwinPrimeSegments (by decide : 119537709 ≤ 120586285)
    (by decide : 120586285 ≤ 121634861) join_2_0 join_2_1

theorem total : (twinPrimeSegment 119537709 121634861).card = 7913 := join_3_0

end S057All
end Sude.GeneratedTwinScan
