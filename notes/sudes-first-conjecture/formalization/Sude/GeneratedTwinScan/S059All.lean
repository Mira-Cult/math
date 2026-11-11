import Sude.GeneratedTwinScan.S059C00
import Sude.GeneratedTwinScan.S059C01
import Sude.GeneratedTwinScan.S059C02
import Sude.GeneratedTwinScan.S059C03
import Sude.GeneratedTwinScan.S059C04
import Sude.GeneratedTwinScan.S059C05
import Sude.GeneratedTwinScan.S059C06
import Sude.GeneratedTwinScan.S059C07
import Sude.GeneratedTwinScan.S059C08
import Sude.GeneratedTwinScan.S059C09
import Sude.GeneratedTwinScan.S059C10
import Sude.GeneratedTwinScan.S059C11
import Sude.GeneratedTwinScan.S059C12
import Sude.GeneratedTwinScan.S059C13
import Sude.GeneratedTwinScan.S059C14
import Sude.GeneratedTwinScan.S059C15

/-! Combined FT source segment; Lean kernel check required. -/
namespace Sude.GeneratedTwinScan
namespace S059All

theorem join_0_0 : (twinPrimeSegment 123732013 123994157).card = 1011 := by
  simpa using combineTwinPrimeSegments (by decide : 123732013 ≤ 123863085)
    (by decide : 123863085 ≤ 123994157) S059C00.total S059C01.total

theorem join_0_1 : (twinPrimeSegment 123994157 124256301).card = 983 := by
  simpa using combineTwinPrimeSegments (by decide : 123994157 ≤ 124125229)
    (by decide : 124125229 ≤ 124256301) S059C02.total S059C03.total

theorem join_0_2 : (twinPrimeSegment 124256301 124518445).card = 982 := by
  simpa using combineTwinPrimeSegments (by decide : 124256301 ≤ 124387373)
    (by decide : 124387373 ≤ 124518445) S059C04.total S059C05.total

theorem join_0_3 : (twinPrimeSegment 124518445 124780589).card = 972 := by
  simpa using combineTwinPrimeSegments (by decide : 124518445 ≤ 124649517)
    (by decide : 124649517 ≤ 124780589) S059C06.total S059C07.total

theorem join_0_4 : (twinPrimeSegment 124780589 125042733).card = 989 := by
  simpa using combineTwinPrimeSegments (by decide : 124780589 ≤ 124911661)
    (by decide : 124911661 ≤ 125042733) S059C08.total S059C09.total

theorem join_0_5 : (twinPrimeSegment 125042733 125304877).card = 980 := by
  simpa using combineTwinPrimeSegments (by decide : 125042733 ≤ 125173805)
    (by decide : 125173805 ≤ 125304877) S059C10.total S059C11.total

theorem join_0_6 : (twinPrimeSegment 125304877 125567021).card = 989 := by
  simpa using combineTwinPrimeSegments (by decide : 125304877 ≤ 125435949)
    (by decide : 125435949 ≤ 125567021) S059C12.total S059C13.total

theorem join_0_7 : (twinPrimeSegment 125567021 125829165).card = 1042 := by
  simpa using combineTwinPrimeSegments (by decide : 125567021 ≤ 125698093)
    (by decide : 125698093 ≤ 125829165) S059C14.total S059C15.total

theorem join_1_0 : (twinPrimeSegment 123732013 124256301).card = 1994 := by
  simpa using combineTwinPrimeSegments (by decide : 123732013 ≤ 123994157)
    (by decide : 123994157 ≤ 124256301) join_0_0 join_0_1

theorem join_1_1 : (twinPrimeSegment 124256301 124780589).card = 1954 := by
  simpa using combineTwinPrimeSegments (by decide : 124256301 ≤ 124518445)
    (by decide : 124518445 ≤ 124780589) join_0_2 join_0_3

theorem join_1_2 : (twinPrimeSegment 124780589 125304877).card = 1969 := by
  simpa using combineTwinPrimeSegments (by decide : 124780589 ≤ 125042733)
    (by decide : 125042733 ≤ 125304877) join_0_4 join_0_5

theorem join_1_3 : (twinPrimeSegment 125304877 125829165).card = 2031 := by
  simpa using combineTwinPrimeSegments (by decide : 125304877 ≤ 125567021)
    (by decide : 125567021 ≤ 125829165) join_0_6 join_0_7

theorem join_2_0 : (twinPrimeSegment 123732013 124780589).card = 3948 := by
  simpa using combineTwinPrimeSegments (by decide : 123732013 ≤ 124256301)
    (by decide : 124256301 ≤ 124780589) join_1_0 join_1_1

theorem join_2_1 : (twinPrimeSegment 124780589 125829165).card = 4000 := by
  simpa using combineTwinPrimeSegments (by decide : 124780589 ≤ 125304877)
    (by decide : 125304877 ≤ 125829165) join_1_2 join_1_3

theorem join_3_0 : (twinPrimeSegment 123732013 125829165).card = 7948 := by
  simpa using combineTwinPrimeSegments (by decide : 123732013 ≤ 124780589)
    (by decide : 124780589 ≤ 125829165) join_2_0 join_2_1

theorem total : (twinPrimeSegment 123732013 125829165).card = 7948 := join_3_0

end S059All
end Sude.GeneratedTwinScan
