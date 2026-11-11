import Sude.GeneratedTwinScan.S028C00
import Sude.GeneratedTwinScan.S028C01
import Sude.GeneratedTwinScan.S028C02
import Sude.GeneratedTwinScan.S028C03
import Sude.GeneratedTwinScan.S028C04
import Sude.GeneratedTwinScan.S028C05
import Sude.GeneratedTwinScan.S028C06
import Sude.GeneratedTwinScan.S028C07
import Sude.GeneratedTwinScan.S028C08
import Sude.GeneratedTwinScan.S028C09
import Sude.GeneratedTwinScan.S028C10
import Sude.GeneratedTwinScan.S028C11
import Sude.GeneratedTwinScan.S028C12
import Sude.GeneratedTwinScan.S028C13
import Sude.GeneratedTwinScan.S028C14
import Sude.GeneratedTwinScan.S028C15

/-! Combined FT source segment; Lean kernel check required. -/
namespace Sude.GeneratedTwinScan
namespace S028All

theorem join_0_0 : (twinPrimeSegment 58720301 58982445).card = 1099 := by
  simpa using combineTwinPrimeSegments (by decide : 58720301 ≤ 58851373)
    (by decide : 58851373 ≤ 58982445) S028C00.total S028C01.total

theorem join_0_1 : (twinPrimeSegment 58982445 59244589).card = 1065 := by
  simpa using combineTwinPrimeSegments (by decide : 58982445 ≤ 59113517)
    (by decide : 59113517 ≤ 59244589) S028C02.total S028C03.total

theorem join_0_2 : (twinPrimeSegment 59244589 59506733).card = 1086 := by
  simpa using combineTwinPrimeSegments (by decide : 59244589 ≤ 59375661)
    (by decide : 59375661 ≤ 59506733) S028C04.total S028C05.total

theorem join_0_3 : (twinPrimeSegment 59506733 59768877).card = 1080 := by
  simpa using combineTwinPrimeSegments (by decide : 59506733 ≤ 59637805)
    (by decide : 59637805 ≤ 59768877) S028C06.total S028C07.total

theorem join_0_4 : (twinPrimeSegment 59768877 60031021).card = 1061 := by
  simpa using combineTwinPrimeSegments (by decide : 59768877 ≤ 59899949)
    (by decide : 59899949 ≤ 60031021) S028C08.total S028C09.total

theorem join_0_5 : (twinPrimeSegment 60031021 60293165).card = 1088 := by
  simpa using combineTwinPrimeSegments (by decide : 60031021 ≤ 60162093)
    (by decide : 60162093 ≤ 60293165) S028C10.total S028C11.total

theorem join_0_6 : (twinPrimeSegment 60293165 60555309).card = 1050 := by
  simpa using combineTwinPrimeSegments (by decide : 60293165 ≤ 60424237)
    (by decide : 60424237 ≤ 60555309) S028C12.total S028C13.total

theorem join_0_7 : (twinPrimeSegment 60555309 60817453).card = 1087 := by
  simpa using combineTwinPrimeSegments (by decide : 60555309 ≤ 60686381)
    (by decide : 60686381 ≤ 60817453) S028C14.total S028C15.total

theorem join_1_0 : (twinPrimeSegment 58720301 59244589).card = 2164 := by
  simpa using combineTwinPrimeSegments (by decide : 58720301 ≤ 58982445)
    (by decide : 58982445 ≤ 59244589) join_0_0 join_0_1

theorem join_1_1 : (twinPrimeSegment 59244589 59768877).card = 2166 := by
  simpa using combineTwinPrimeSegments (by decide : 59244589 ≤ 59506733)
    (by decide : 59506733 ≤ 59768877) join_0_2 join_0_3

theorem join_1_2 : (twinPrimeSegment 59768877 60293165).card = 2149 := by
  simpa using combineTwinPrimeSegments (by decide : 59768877 ≤ 60031021)
    (by decide : 60031021 ≤ 60293165) join_0_4 join_0_5

theorem join_1_3 : (twinPrimeSegment 60293165 60817453).card = 2137 := by
  simpa using combineTwinPrimeSegments (by decide : 60293165 ≤ 60555309)
    (by decide : 60555309 ≤ 60817453) join_0_6 join_0_7

theorem join_2_0 : (twinPrimeSegment 58720301 59768877).card = 4330 := by
  simpa using combineTwinPrimeSegments (by decide : 58720301 ≤ 59244589)
    (by decide : 59244589 ≤ 59768877) join_1_0 join_1_1

theorem join_2_1 : (twinPrimeSegment 59768877 60817453).card = 4286 := by
  simpa using combineTwinPrimeSegments (by decide : 59768877 ≤ 60293165)
    (by decide : 60293165 ≤ 60817453) join_1_2 join_1_3

theorem join_3_0 : (twinPrimeSegment 58720301 60817453).card = 8616 := by
  simpa using combineTwinPrimeSegments (by decide : 58720301 ≤ 59768877)
    (by decide : 59768877 ≤ 60817453) join_2_0 join_2_1

theorem total : (twinPrimeSegment 58720301 60817453).card = 8616 := join_3_0

end S028All
end Sude.GeneratedTwinScan
