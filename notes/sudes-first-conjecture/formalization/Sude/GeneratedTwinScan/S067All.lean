import Sude.GeneratedTwinScan.S067C00
import Sude.GeneratedTwinScan.S067C01
import Sude.GeneratedTwinScan.S067C02
import Sude.GeneratedTwinScan.S067C03
import Sude.GeneratedTwinScan.S067C04
import Sude.GeneratedTwinScan.S067C05
import Sude.GeneratedTwinScan.S067C06
import Sude.GeneratedTwinScan.S067C07
import Sude.GeneratedTwinScan.S067C08
import Sude.GeneratedTwinScan.S067C09
import Sude.GeneratedTwinScan.S067C10
import Sude.GeneratedTwinScan.S067C11
import Sude.GeneratedTwinScan.S067C12
import Sude.GeneratedTwinScan.S067C13
import Sude.GeneratedTwinScan.S067C14
import Sude.GeneratedTwinScan.S067C15

/-! Combined FT source segment; Lean kernel check required. -/
namespace Sude.GeneratedTwinScan
namespace S067All

theorem join_0_0 : (twinPrimeSegment 140509229 140771373).card = 986 := by
  simpa using combineTwinPrimeSegments (by decide : 140509229 ≤ 140640301)
    (by decide : 140640301 ≤ 140771373) S067C00.total S067C01.total

theorem join_0_1 : (twinPrimeSegment 140771373 141033517).card = 974 := by
  simpa using combineTwinPrimeSegments (by decide : 140771373 ≤ 140902445)
    (by decide : 140902445 ≤ 141033517) S067C02.total S067C03.total

theorem join_0_2 : (twinPrimeSegment 141033517 141295661).card = 942 := by
  simpa using combineTwinPrimeSegments (by decide : 141033517 ≤ 141164589)
    (by decide : 141164589 ≤ 141295661) S067C04.total S067C05.total

theorem join_0_3 : (twinPrimeSegment 141295661 141557805).card = 1022 := by
  simpa using combineTwinPrimeSegments (by decide : 141295661 ≤ 141426733)
    (by decide : 141426733 ≤ 141557805) S067C06.total S067C07.total

theorem join_0_4 : (twinPrimeSegment 141557805 141819949).card = 955 := by
  simpa using combineTwinPrimeSegments (by decide : 141557805 ≤ 141688877)
    (by decide : 141688877 ≤ 141819949) S067C08.total S067C09.total

theorem join_0_5 : (twinPrimeSegment 141819949 142082093).card = 999 := by
  simpa using combineTwinPrimeSegments (by decide : 141819949 ≤ 141951021)
    (by decide : 141951021 ≤ 142082093) S067C10.total S067C11.total

theorem join_0_6 : (twinPrimeSegment 142082093 142344237).card = 929 := by
  simpa using combineTwinPrimeSegments (by decide : 142082093 ≤ 142213165)
    (by decide : 142213165 ≤ 142344237) S067C12.total S067C13.total

theorem join_0_7 : (twinPrimeSegment 142344237 142606381).card = 987 := by
  simpa using combineTwinPrimeSegments (by decide : 142344237 ≤ 142475309)
    (by decide : 142475309 ≤ 142606381) S067C14.total S067C15.total

theorem join_1_0 : (twinPrimeSegment 140509229 141033517).card = 1960 := by
  simpa using combineTwinPrimeSegments (by decide : 140509229 ≤ 140771373)
    (by decide : 140771373 ≤ 141033517) join_0_0 join_0_1

theorem join_1_1 : (twinPrimeSegment 141033517 141557805).card = 1964 := by
  simpa using combineTwinPrimeSegments (by decide : 141033517 ≤ 141295661)
    (by decide : 141295661 ≤ 141557805) join_0_2 join_0_3

theorem join_1_2 : (twinPrimeSegment 141557805 142082093).card = 1954 := by
  simpa using combineTwinPrimeSegments (by decide : 141557805 ≤ 141819949)
    (by decide : 141819949 ≤ 142082093) join_0_4 join_0_5

theorem join_1_3 : (twinPrimeSegment 142082093 142606381).card = 1916 := by
  simpa using combineTwinPrimeSegments (by decide : 142082093 ≤ 142344237)
    (by decide : 142344237 ≤ 142606381) join_0_6 join_0_7

theorem join_2_0 : (twinPrimeSegment 140509229 141557805).card = 3924 := by
  simpa using combineTwinPrimeSegments (by decide : 140509229 ≤ 141033517)
    (by decide : 141033517 ≤ 141557805) join_1_0 join_1_1

theorem join_2_1 : (twinPrimeSegment 141557805 142606381).card = 3870 := by
  simpa using combineTwinPrimeSegments (by decide : 141557805 ≤ 142082093)
    (by decide : 142082093 ≤ 142606381) join_1_2 join_1_3

theorem join_3_0 : (twinPrimeSegment 140509229 142606381).card = 7794 := by
  simpa using combineTwinPrimeSegments (by decide : 140509229 ≤ 141557805)
    (by decide : 141557805 ≤ 142606381) join_2_0 join_2_1

theorem total : (twinPrimeSegment 140509229 142606381).card = 7794 := join_3_0

end S067All
end Sude.GeneratedTwinScan
