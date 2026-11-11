import Sude.GeneratedTwinScan.S153C00
import Sude.GeneratedTwinScan.S153C01
import Sude.GeneratedTwinScan.S153C02
import Sude.GeneratedTwinScan.S153C03
import Sude.GeneratedTwinScan.S153C04
import Sude.GeneratedTwinScan.S153C05
import Sude.GeneratedTwinScan.S153C06
import Sude.GeneratedTwinScan.S153C07
import Sude.GeneratedTwinScan.S153C08
import Sude.GeneratedTwinScan.S153C09
import Sude.GeneratedTwinScan.S153C10
import Sude.GeneratedTwinScan.S153C11
import Sude.GeneratedTwinScan.S153C12
import Sude.GeneratedTwinScan.S153C13
import Sude.GeneratedTwinScan.S153C14
import Sude.GeneratedTwinScan.S153C15

/-! Combined FT source segment; Lean kernel check required. -/
namespace Sude.GeneratedTwinScan
namespace S153All

theorem join_0_0 : (twinPrimeSegment 320864301 321126445).card = 859 := by
  simpa using combineTwinPrimeSegments (by decide : 320864301 ≤ 320995373)
    (by decide : 320995373 ≤ 321126445) S153C00.total S153C01.total

theorem join_0_1 : (twinPrimeSegment 321126445 321388589).card = 885 := by
  simpa using combineTwinPrimeSegments (by decide : 321126445 ≤ 321257517)
    (by decide : 321257517 ≤ 321388589) S153C02.total S153C03.total

theorem join_0_2 : (twinPrimeSegment 321388589 321650733).card = 883 := by
  simpa using combineTwinPrimeSegments (by decide : 321388589 ≤ 321519661)
    (by decide : 321519661 ≤ 321650733) S153C04.total S153C05.total

theorem join_0_3 : (twinPrimeSegment 321650733 321912877).card = 882 := by
  simpa using combineTwinPrimeSegments (by decide : 321650733 ≤ 321781805)
    (by decide : 321781805 ≤ 321912877) S153C06.total S153C07.total

theorem join_0_4 : (twinPrimeSegment 321912877 322175021).card = 920 := by
  simpa using combineTwinPrimeSegments (by decide : 321912877 ≤ 322043949)
    (by decide : 322043949 ≤ 322175021) S153C08.total S153C09.total

theorem join_0_5 : (twinPrimeSegment 322175021 322437165).card = 939 := by
  simpa using combineTwinPrimeSegments (by decide : 322175021 ≤ 322306093)
    (by decide : 322306093 ≤ 322437165) S153C10.total S153C11.total

theorem join_0_6 : (twinPrimeSegment 322437165 322699309).card = 908 := by
  simpa using combineTwinPrimeSegments (by decide : 322437165 ≤ 322568237)
    (by decide : 322568237 ≤ 322699309) S153C12.total S153C13.total

theorem join_0_7 : (twinPrimeSegment 322699309 322961453).card = 914 := by
  simpa using combineTwinPrimeSegments (by decide : 322699309 ≤ 322830381)
    (by decide : 322830381 ≤ 322961453) S153C14.total S153C15.total

theorem join_1_0 : (twinPrimeSegment 320864301 321388589).card = 1744 := by
  simpa using combineTwinPrimeSegments (by decide : 320864301 ≤ 321126445)
    (by decide : 321126445 ≤ 321388589) join_0_0 join_0_1

theorem join_1_1 : (twinPrimeSegment 321388589 321912877).card = 1765 := by
  simpa using combineTwinPrimeSegments (by decide : 321388589 ≤ 321650733)
    (by decide : 321650733 ≤ 321912877) join_0_2 join_0_3

theorem join_1_2 : (twinPrimeSegment 321912877 322437165).card = 1859 := by
  simpa using combineTwinPrimeSegments (by decide : 321912877 ≤ 322175021)
    (by decide : 322175021 ≤ 322437165) join_0_4 join_0_5

theorem join_1_3 : (twinPrimeSegment 322437165 322961453).card = 1822 := by
  simpa using combineTwinPrimeSegments (by decide : 322437165 ≤ 322699309)
    (by decide : 322699309 ≤ 322961453) join_0_6 join_0_7

theorem join_2_0 : (twinPrimeSegment 320864301 321912877).card = 3509 := by
  simpa using combineTwinPrimeSegments (by decide : 320864301 ≤ 321388589)
    (by decide : 321388589 ≤ 321912877) join_1_0 join_1_1

theorem join_2_1 : (twinPrimeSegment 321912877 322961453).card = 3681 := by
  simpa using combineTwinPrimeSegments (by decide : 321912877 ≤ 322437165)
    (by decide : 322437165 ≤ 322961453) join_1_2 join_1_3

theorem join_3_0 : (twinPrimeSegment 320864301 322961453).card = 7190 := by
  simpa using combineTwinPrimeSegments (by decide : 320864301 ≤ 321912877)
    (by decide : 321912877 ≤ 322961453) join_2_0 join_2_1

theorem total : (twinPrimeSegment 320864301 322961453).card = 7190 := join_3_0

end S153All
end Sude.GeneratedTwinScan
