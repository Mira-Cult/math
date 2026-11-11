import Sude.GeneratedTwinScan.S062C00
import Sude.GeneratedTwinScan.S062C01
import Sude.GeneratedTwinScan.S062C02
import Sude.GeneratedTwinScan.S062C03
import Sude.GeneratedTwinScan.S062C04
import Sude.GeneratedTwinScan.S062C05
import Sude.GeneratedTwinScan.S062C06
import Sude.GeneratedTwinScan.S062C07
import Sude.GeneratedTwinScan.S062C08
import Sude.GeneratedTwinScan.S062C09
import Sude.GeneratedTwinScan.S062C10
import Sude.GeneratedTwinScan.S062C11
import Sude.GeneratedTwinScan.S062C12
import Sude.GeneratedTwinScan.S062C13
import Sude.GeneratedTwinScan.S062C14
import Sude.GeneratedTwinScan.S062C15

/-! Combined FT source segment; Lean kernel check required. -/
namespace Sude.GeneratedTwinScan
namespace S062All

theorem join_0_0 : (twinPrimeSegment 130023469 130285613).card = 988 := by
  simpa using combineTwinPrimeSegments (by decide : 130023469 ≤ 130154541)
    (by decide : 130154541 ≤ 130285613) S062C00.total S062C01.total

theorem join_0_1 : (twinPrimeSegment 130285613 130547757).card = 963 := by
  simpa using combineTwinPrimeSegments (by decide : 130285613 ≤ 130416685)
    (by decide : 130416685 ≤ 130547757) S062C02.total S062C03.total

theorem join_0_2 : (twinPrimeSegment 130547757 130809901).card = 999 := by
  simpa using combineTwinPrimeSegments (by decide : 130547757 ≤ 130678829)
    (by decide : 130678829 ≤ 130809901) S062C04.total S062C05.total

theorem join_0_3 : (twinPrimeSegment 130809901 131072045).card = 984 := by
  simpa using combineTwinPrimeSegments (by decide : 130809901 ≤ 130940973)
    (by decide : 130940973 ≤ 131072045) S062C06.total S062C07.total

theorem join_0_4 : (twinPrimeSegment 131072045 131334189).card = 955 := by
  simpa using combineTwinPrimeSegments (by decide : 131072045 ≤ 131203117)
    (by decide : 131203117 ≤ 131334189) S062C08.total S062C09.total

theorem join_0_5 : (twinPrimeSegment 131334189 131596333).card = 1024 := by
  simpa using combineTwinPrimeSegments (by decide : 131334189 ≤ 131465261)
    (by decide : 131465261 ≤ 131596333) S062C10.total S062C11.total

theorem join_0_6 : (twinPrimeSegment 131596333 131858477).card = 985 := by
  simpa using combineTwinPrimeSegments (by decide : 131596333 ≤ 131727405)
    (by decide : 131727405 ≤ 131858477) S062C12.total S062C13.total

theorem join_0_7 : (twinPrimeSegment 131858477 132120621).card = 1045 := by
  simpa using combineTwinPrimeSegments (by decide : 131858477 ≤ 131989549)
    (by decide : 131989549 ≤ 132120621) S062C14.total S062C15.total

theorem join_1_0 : (twinPrimeSegment 130023469 130547757).card = 1951 := by
  simpa using combineTwinPrimeSegments (by decide : 130023469 ≤ 130285613)
    (by decide : 130285613 ≤ 130547757) join_0_0 join_0_1

theorem join_1_1 : (twinPrimeSegment 130547757 131072045).card = 1983 := by
  simpa using combineTwinPrimeSegments (by decide : 130547757 ≤ 130809901)
    (by decide : 130809901 ≤ 131072045) join_0_2 join_0_3

theorem join_1_2 : (twinPrimeSegment 131072045 131596333).card = 1979 := by
  simpa using combineTwinPrimeSegments (by decide : 131072045 ≤ 131334189)
    (by decide : 131334189 ≤ 131596333) join_0_4 join_0_5

theorem join_1_3 : (twinPrimeSegment 131596333 132120621).card = 2030 := by
  simpa using combineTwinPrimeSegments (by decide : 131596333 ≤ 131858477)
    (by decide : 131858477 ≤ 132120621) join_0_6 join_0_7

theorem join_2_0 : (twinPrimeSegment 130023469 131072045).card = 3934 := by
  simpa using combineTwinPrimeSegments (by decide : 130023469 ≤ 130547757)
    (by decide : 130547757 ≤ 131072045) join_1_0 join_1_1

theorem join_2_1 : (twinPrimeSegment 131072045 132120621).card = 4009 := by
  simpa using combineTwinPrimeSegments (by decide : 131072045 ≤ 131596333)
    (by decide : 131596333 ≤ 132120621) join_1_2 join_1_3

theorem join_3_0 : (twinPrimeSegment 130023469 132120621).card = 7943 := by
  simpa using combineTwinPrimeSegments (by decide : 130023469 ≤ 131072045)
    (by decide : 131072045 ≤ 132120621) join_2_0 join_2_1

theorem total : (twinPrimeSegment 130023469 132120621).card = 7943 := join_3_0

end S062All
end Sude.GeneratedTwinScan
