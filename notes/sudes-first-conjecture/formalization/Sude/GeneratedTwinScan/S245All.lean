import Sude.GeneratedTwinScan.S245C00
import Sude.GeneratedTwinScan.S245C01
import Sude.GeneratedTwinScan.S245C02
import Sude.GeneratedTwinScan.S245C03
import Sude.GeneratedTwinScan.S245C04
import Sude.GeneratedTwinScan.S245C05
import Sude.GeneratedTwinScan.S245C06
import Sude.GeneratedTwinScan.S245C07
import Sude.GeneratedTwinScan.S245C08
import Sude.GeneratedTwinScan.S245C09
import Sude.GeneratedTwinScan.S245C10
import Sude.GeneratedTwinScan.S245C11
import Sude.GeneratedTwinScan.S245C12
import Sude.GeneratedTwinScan.S245C13
import Sude.GeneratedTwinScan.S245C14
import Sude.GeneratedTwinScan.S245C15

/-! Combined FT source segment; Lean kernel check required. -/
namespace Sude.GeneratedTwinScan
namespace S245All

theorem join_0_0 : (twinPrimeSegment 513802285 514064429).card = 866 := by
  simpa using combineTwinPrimeSegments (by decide : 513802285 ≤ 513933357)
    (by decide : 513933357 ≤ 514064429) S245C00.total S245C01.total

theorem join_0_1 : (twinPrimeSegment 514064429 514326573).card = 887 := by
  simpa using combineTwinPrimeSegments (by decide : 514064429 ≤ 514195501)
    (by decide : 514195501 ≤ 514326573) S245C02.total S245C03.total

theorem join_0_2 : (twinPrimeSegment 514326573 514588717).card = 866 := by
  simpa using combineTwinPrimeSegments (by decide : 514326573 ≤ 514457645)
    (by decide : 514457645 ≤ 514588717) S245C04.total S245C05.total

theorem join_0_3 : (twinPrimeSegment 514588717 514850861).card = 809 := by
  simpa using combineTwinPrimeSegments (by decide : 514588717 ≤ 514719789)
    (by decide : 514719789 ≤ 514850861) S245C06.total S245C07.total

theorem join_0_4 : (twinPrimeSegment 514850861 515113005).card = 865 := by
  simpa using combineTwinPrimeSegments (by decide : 514850861 ≤ 514981933)
    (by decide : 514981933 ≤ 515113005) S245C08.total S245C09.total

theorem join_0_5 : (twinPrimeSegment 515113005 515375149).card = 824 := by
  simpa using combineTwinPrimeSegments (by decide : 515113005 ≤ 515244077)
    (by decide : 515244077 ≤ 515375149) S245C10.total S245C11.total

theorem join_0_6 : (twinPrimeSegment 515375149 515637293).card = 857 := by
  simpa using combineTwinPrimeSegments (by decide : 515375149 ≤ 515506221)
    (by decide : 515506221 ≤ 515637293) S245C12.total S245C13.total

theorem join_0_7 : (twinPrimeSegment 515637293 515899437).card = 893 := by
  simpa using combineTwinPrimeSegments (by decide : 515637293 ≤ 515768365)
    (by decide : 515768365 ≤ 515899437) S245C14.total S245C15.total

theorem join_1_0 : (twinPrimeSegment 513802285 514326573).card = 1753 := by
  simpa using combineTwinPrimeSegments (by decide : 513802285 ≤ 514064429)
    (by decide : 514064429 ≤ 514326573) join_0_0 join_0_1

theorem join_1_1 : (twinPrimeSegment 514326573 514850861).card = 1675 := by
  simpa using combineTwinPrimeSegments (by decide : 514326573 ≤ 514588717)
    (by decide : 514588717 ≤ 514850861) join_0_2 join_0_3

theorem join_1_2 : (twinPrimeSegment 514850861 515375149).card = 1689 := by
  simpa using combineTwinPrimeSegments (by decide : 514850861 ≤ 515113005)
    (by decide : 515113005 ≤ 515375149) join_0_4 join_0_5

theorem join_1_3 : (twinPrimeSegment 515375149 515899437).card = 1750 := by
  simpa using combineTwinPrimeSegments (by decide : 515375149 ≤ 515637293)
    (by decide : 515637293 ≤ 515899437) join_0_6 join_0_7

theorem join_2_0 : (twinPrimeSegment 513802285 514850861).card = 3428 := by
  simpa using combineTwinPrimeSegments (by decide : 513802285 ≤ 514326573)
    (by decide : 514326573 ≤ 514850861) join_1_0 join_1_1

theorem join_2_1 : (twinPrimeSegment 514850861 515899437).card = 3439 := by
  simpa using combineTwinPrimeSegments (by decide : 514850861 ≤ 515375149)
    (by decide : 515375149 ≤ 515899437) join_1_2 join_1_3

theorem join_3_0 : (twinPrimeSegment 513802285 515899437).card = 6867 := by
  simpa using combineTwinPrimeSegments (by decide : 513802285 ≤ 514850861)
    (by decide : 514850861 ≤ 515899437) join_2_0 join_2_1

theorem total : (twinPrimeSegment 513802285 515899437).card = 6867 := join_3_0

end S245All
end Sude.GeneratedTwinScan
