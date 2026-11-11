import Sude.GeneratedTwinScan.S090C00
import Sude.GeneratedTwinScan.S090C01
import Sude.GeneratedTwinScan.S090C02
import Sude.GeneratedTwinScan.S090C03
import Sude.GeneratedTwinScan.S090C04
import Sude.GeneratedTwinScan.S090C05
import Sude.GeneratedTwinScan.S090C06
import Sude.GeneratedTwinScan.S090C07
import Sude.GeneratedTwinScan.S090C08
import Sude.GeneratedTwinScan.S090C09
import Sude.GeneratedTwinScan.S090C10
import Sude.GeneratedTwinScan.S090C11
import Sude.GeneratedTwinScan.S090C12
import Sude.GeneratedTwinScan.S090C13
import Sude.GeneratedTwinScan.S090C14
import Sude.GeneratedTwinScan.S090C15

/-! Combined FT source segment; Lean kernel check required. -/
namespace Sude.GeneratedTwinScan
namespace S090All

theorem join_0_0 : (twinPrimeSegment 188743725 189005869).card = 923 := by
  simpa using combineTwinPrimeSegments (by decide : 188743725 ≤ 188874797)
    (by decide : 188874797 ≤ 189005869) S090C00.total S090C01.total

theorem join_0_1 : (twinPrimeSegment 189005869 189268013).card = 978 := by
  simpa using combineTwinPrimeSegments (by decide : 189005869 ≤ 189136941)
    (by decide : 189136941 ≤ 189268013) S090C02.total S090C03.total

theorem join_0_2 : (twinPrimeSegment 189268013 189530157).card = 925 := by
  simpa using combineTwinPrimeSegments (by decide : 189268013 ≤ 189399085)
    (by decide : 189399085 ≤ 189530157) S090C04.total S090C05.total

theorem join_0_3 : (twinPrimeSegment 189530157 189792301).card = 960 := by
  simpa using combineTwinPrimeSegments (by decide : 189530157 ≤ 189661229)
    (by decide : 189661229 ≤ 189792301) S090C06.total S090C07.total

theorem join_0_4 : (twinPrimeSegment 189792301 190054445).card = 1001 := by
  simpa using combineTwinPrimeSegments (by decide : 189792301 ≤ 189923373)
    (by decide : 189923373 ≤ 190054445) S090C08.total S090C09.total

theorem join_0_5 : (twinPrimeSegment 190054445 190316589).card = 942 := by
  simpa using combineTwinPrimeSegments (by decide : 190054445 ≤ 190185517)
    (by decide : 190185517 ≤ 190316589) S090C10.total S090C11.total

theorem join_0_6 : (twinPrimeSegment 190316589 190578733).card = 924 := by
  simpa using combineTwinPrimeSegments (by decide : 190316589 ≤ 190447661)
    (by decide : 190447661 ≤ 190578733) S090C12.total S090C13.total

theorem join_0_7 : (twinPrimeSegment 190578733 190840877).card = 933 := by
  simpa using combineTwinPrimeSegments (by decide : 190578733 ≤ 190709805)
    (by decide : 190709805 ≤ 190840877) S090C14.total S090C15.total

theorem join_1_0 : (twinPrimeSegment 188743725 189268013).card = 1901 := by
  simpa using combineTwinPrimeSegments (by decide : 188743725 ≤ 189005869)
    (by decide : 189005869 ≤ 189268013) join_0_0 join_0_1

theorem join_1_1 : (twinPrimeSegment 189268013 189792301).card = 1885 := by
  simpa using combineTwinPrimeSegments (by decide : 189268013 ≤ 189530157)
    (by decide : 189530157 ≤ 189792301) join_0_2 join_0_3

theorem join_1_2 : (twinPrimeSegment 189792301 190316589).card = 1943 := by
  simpa using combineTwinPrimeSegments (by decide : 189792301 ≤ 190054445)
    (by decide : 190054445 ≤ 190316589) join_0_4 join_0_5

theorem join_1_3 : (twinPrimeSegment 190316589 190840877).card = 1857 := by
  simpa using combineTwinPrimeSegments (by decide : 190316589 ≤ 190578733)
    (by decide : 190578733 ≤ 190840877) join_0_6 join_0_7

theorem join_2_0 : (twinPrimeSegment 188743725 189792301).card = 3786 := by
  simpa using combineTwinPrimeSegments (by decide : 188743725 ≤ 189268013)
    (by decide : 189268013 ≤ 189792301) join_1_0 join_1_1

theorem join_2_1 : (twinPrimeSegment 189792301 190840877).card = 3800 := by
  simpa using combineTwinPrimeSegments (by decide : 189792301 ≤ 190316589)
    (by decide : 190316589 ≤ 190840877) join_1_2 join_1_3

theorem join_3_0 : (twinPrimeSegment 188743725 190840877).card = 7586 := by
  simpa using combineTwinPrimeSegments (by decide : 188743725 ≤ 189792301)
    (by decide : 189792301 ≤ 190840877) join_2_0 join_2_1

theorem total : (twinPrimeSegment 188743725 190840877).card = 7586 := join_3_0

end S090All
end Sude.GeneratedTwinScan
