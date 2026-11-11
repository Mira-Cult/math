import Sude.GeneratedTwinScan.S093C00
import Sude.GeneratedTwinScan.S093C01
import Sude.GeneratedTwinScan.S093C02
import Sude.GeneratedTwinScan.S093C03
import Sude.GeneratedTwinScan.S093C04
import Sude.GeneratedTwinScan.S093C05
import Sude.GeneratedTwinScan.S093C06
import Sude.GeneratedTwinScan.S093C07
import Sude.GeneratedTwinScan.S093C08
import Sude.GeneratedTwinScan.S093C09
import Sude.GeneratedTwinScan.S093C10
import Sude.GeneratedTwinScan.S093C11
import Sude.GeneratedTwinScan.S093C12
import Sude.GeneratedTwinScan.S093C13
import Sude.GeneratedTwinScan.S093C14
import Sude.GeneratedTwinScan.S093C15

/-! Combined FT source segment; Lean kernel check required. -/
namespace Sude.GeneratedTwinScan
namespace S093All

theorem join_0_0 : (twinPrimeSegment 195035181 195297325).card = 971 := by
  simpa using combineTwinPrimeSegments (by decide : 195035181 ≤ 195166253)
    (by decide : 195166253 ≤ 195297325) S093C00.total S093C01.total

theorem join_0_1 : (twinPrimeSegment 195297325 195559469).card = 941 := by
  simpa using combineTwinPrimeSegments (by decide : 195297325 ≤ 195428397)
    (by decide : 195428397 ≤ 195559469) S093C02.total S093C03.total

theorem join_0_2 : (twinPrimeSegment 195559469 195821613).card = 919 := by
  simpa using combineTwinPrimeSegments (by decide : 195559469 ≤ 195690541)
    (by decide : 195690541 ≤ 195821613) S093C04.total S093C05.total

theorem join_0_3 : (twinPrimeSegment 195821613 196083757).card = 965 := by
  simpa using combineTwinPrimeSegments (by decide : 195821613 ≤ 195952685)
    (by decide : 195952685 ≤ 196083757) S093C06.total S093C07.total

theorem join_0_4 : (twinPrimeSegment 196083757 196345901).card = 957 := by
  simpa using combineTwinPrimeSegments (by decide : 196083757 ≤ 196214829)
    (by decide : 196214829 ≤ 196345901) S093C08.total S093C09.total

theorem join_0_5 : (twinPrimeSegment 196345901 196608045).card = 945 := by
  simpa using combineTwinPrimeSegments (by decide : 196345901 ≤ 196476973)
    (by decide : 196476973 ≤ 196608045) S093C10.total S093C11.total

theorem join_0_6 : (twinPrimeSegment 196608045 196870189).card = 945 := by
  simpa using combineTwinPrimeSegments (by decide : 196608045 ≤ 196739117)
    (by decide : 196739117 ≤ 196870189) S093C12.total S093C13.total

theorem join_0_7 : (twinPrimeSegment 196870189 197132333).card = 918 := by
  simpa using combineTwinPrimeSegments (by decide : 196870189 ≤ 197001261)
    (by decide : 197001261 ≤ 197132333) S093C14.total S093C15.total

theorem join_1_0 : (twinPrimeSegment 195035181 195559469).card = 1912 := by
  simpa using combineTwinPrimeSegments (by decide : 195035181 ≤ 195297325)
    (by decide : 195297325 ≤ 195559469) join_0_0 join_0_1

theorem join_1_1 : (twinPrimeSegment 195559469 196083757).card = 1884 := by
  simpa using combineTwinPrimeSegments (by decide : 195559469 ≤ 195821613)
    (by decide : 195821613 ≤ 196083757) join_0_2 join_0_3

theorem join_1_2 : (twinPrimeSegment 196083757 196608045).card = 1902 := by
  simpa using combineTwinPrimeSegments (by decide : 196083757 ≤ 196345901)
    (by decide : 196345901 ≤ 196608045) join_0_4 join_0_5

theorem join_1_3 : (twinPrimeSegment 196608045 197132333).card = 1863 := by
  simpa using combineTwinPrimeSegments (by decide : 196608045 ≤ 196870189)
    (by decide : 196870189 ≤ 197132333) join_0_6 join_0_7

theorem join_2_0 : (twinPrimeSegment 195035181 196083757).card = 3796 := by
  simpa using combineTwinPrimeSegments (by decide : 195035181 ≤ 195559469)
    (by decide : 195559469 ≤ 196083757) join_1_0 join_1_1

theorem join_2_1 : (twinPrimeSegment 196083757 197132333).card = 3765 := by
  simpa using combineTwinPrimeSegments (by decide : 196083757 ≤ 196608045)
    (by decide : 196608045 ≤ 197132333) join_1_2 join_1_3

theorem join_3_0 : (twinPrimeSegment 195035181 197132333).card = 7561 := by
  simpa using combineTwinPrimeSegments (by decide : 195035181 ≤ 196083757)
    (by decide : 196083757 ≤ 197132333) join_2_0 join_2_1

theorem total : (twinPrimeSegment 195035181 197132333).card = 7561 := join_3_0

end S093All
end Sude.GeneratedTwinScan
