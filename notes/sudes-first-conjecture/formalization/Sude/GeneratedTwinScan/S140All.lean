import Sude.GeneratedTwinScan.S140C00
import Sude.GeneratedTwinScan.S140C01
import Sude.GeneratedTwinScan.S140C02
import Sude.GeneratedTwinScan.S140C03
import Sude.GeneratedTwinScan.S140C04
import Sude.GeneratedTwinScan.S140C05
import Sude.GeneratedTwinScan.S140C06
import Sude.GeneratedTwinScan.S140C07
import Sude.GeneratedTwinScan.S140C08
import Sude.GeneratedTwinScan.S140C09
import Sude.GeneratedTwinScan.S140C10
import Sude.GeneratedTwinScan.S140C11
import Sude.GeneratedTwinScan.S140C12
import Sude.GeneratedTwinScan.S140C13
import Sude.GeneratedTwinScan.S140C14
import Sude.GeneratedTwinScan.S140C15

/-! Combined FT source segment; Lean kernel check required. -/
namespace Sude.GeneratedTwinScan
namespace S140All

theorem join_0_0 : (twinPrimeSegment 293601325 293863469).card = 916 := by
  simpa using combineTwinPrimeSegments (by decide : 293601325 ≤ 293732397)
    (by decide : 293732397 ≤ 293863469) S140C00.total S140C01.total

theorem join_0_1 : (twinPrimeSegment 293863469 294125613).card = 919 := by
  simpa using combineTwinPrimeSegments (by decide : 293863469 ≤ 293994541)
    (by decide : 293994541 ≤ 294125613) S140C02.total S140C03.total

theorem join_0_2 : (twinPrimeSegment 294125613 294387757).card = 960 := by
  simpa using combineTwinPrimeSegments (by decide : 294125613 ≤ 294256685)
    (by decide : 294256685 ≤ 294387757) S140C04.total S140C05.total

theorem join_0_3 : (twinPrimeSegment 294387757 294649901).card = 909 := by
  simpa using combineTwinPrimeSegments (by decide : 294387757 ≤ 294518829)
    (by decide : 294518829 ≤ 294649901) S140C06.total S140C07.total

theorem join_0_4 : (twinPrimeSegment 294649901 294912045).card = 879 := by
  simpa using combineTwinPrimeSegments (by decide : 294649901 ≤ 294780973)
    (by decide : 294780973 ≤ 294912045) S140C08.total S140C09.total

theorem join_0_5 : (twinPrimeSegment 294912045 295174189).card = 879 := by
  simpa using combineTwinPrimeSegments (by decide : 294912045 ≤ 295043117)
    (by decide : 295043117 ≤ 295174189) S140C10.total S140C11.total

theorem join_0_6 : (twinPrimeSegment 295174189 295436333).card = 933 := by
  simpa using combineTwinPrimeSegments (by decide : 295174189 ≤ 295305261)
    (by decide : 295305261 ≤ 295436333) S140C12.total S140C13.total

theorem join_0_7 : (twinPrimeSegment 295436333 295698477).card = 950 := by
  simpa using combineTwinPrimeSegments (by decide : 295436333 ≤ 295567405)
    (by decide : 295567405 ≤ 295698477) S140C14.total S140C15.total

theorem join_1_0 : (twinPrimeSegment 293601325 294125613).card = 1835 := by
  simpa using combineTwinPrimeSegments (by decide : 293601325 ≤ 293863469)
    (by decide : 293863469 ≤ 294125613) join_0_0 join_0_1

theorem join_1_1 : (twinPrimeSegment 294125613 294649901).card = 1869 := by
  simpa using combineTwinPrimeSegments (by decide : 294125613 ≤ 294387757)
    (by decide : 294387757 ≤ 294649901) join_0_2 join_0_3

theorem join_1_2 : (twinPrimeSegment 294649901 295174189).card = 1758 := by
  simpa using combineTwinPrimeSegments (by decide : 294649901 ≤ 294912045)
    (by decide : 294912045 ≤ 295174189) join_0_4 join_0_5

theorem join_1_3 : (twinPrimeSegment 295174189 295698477).card = 1883 := by
  simpa using combineTwinPrimeSegments (by decide : 295174189 ≤ 295436333)
    (by decide : 295436333 ≤ 295698477) join_0_6 join_0_7

theorem join_2_0 : (twinPrimeSegment 293601325 294649901).card = 3704 := by
  simpa using combineTwinPrimeSegments (by decide : 293601325 ≤ 294125613)
    (by decide : 294125613 ≤ 294649901) join_1_0 join_1_1

theorem join_2_1 : (twinPrimeSegment 294649901 295698477).card = 3641 := by
  simpa using combineTwinPrimeSegments (by decide : 294649901 ≤ 295174189)
    (by decide : 295174189 ≤ 295698477) join_1_2 join_1_3

theorem join_3_0 : (twinPrimeSegment 293601325 295698477).card = 7345 := by
  simpa using combineTwinPrimeSegments (by decide : 293601325 ≤ 294649901)
    (by decide : 294649901 ≤ 295698477) join_2_0 join_2_1

theorem total : (twinPrimeSegment 293601325 295698477).card = 7345 := join_3_0

end S140All
end Sude.GeneratedTwinScan
