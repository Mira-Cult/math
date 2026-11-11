import Sude.GeneratedTwinScan.S015C00
import Sude.GeneratedTwinScan.S015C01
import Sude.GeneratedTwinScan.S015C02
import Sude.GeneratedTwinScan.S015C03
import Sude.GeneratedTwinScan.S015C04
import Sude.GeneratedTwinScan.S015C05
import Sude.GeneratedTwinScan.S015C06
import Sude.GeneratedTwinScan.S015C07
import Sude.GeneratedTwinScan.S015C08
import Sude.GeneratedTwinScan.S015C09
import Sude.GeneratedTwinScan.S015C10
import Sude.GeneratedTwinScan.S015C11
import Sude.GeneratedTwinScan.S015C12
import Sude.GeneratedTwinScan.S015C13
import Sude.GeneratedTwinScan.S015C14
import Sude.GeneratedTwinScan.S015C15

/-! Combined FT source segment; Lean kernel check required. -/
namespace Sude.GeneratedTwinScan
namespace S015All

theorem join_0_0 : (twinPrimeSegment 31457325 31719469).card = 1173 := by
  simpa using combineTwinPrimeSegments (by decide : 31457325 ≤ 31588397)
    (by decide : 31588397 ≤ 31719469) S015C00.total S015C01.total

theorem join_0_1 : (twinPrimeSegment 31719469 31981613).card = 1163 := by
  simpa using combineTwinPrimeSegments (by decide : 31719469 ≤ 31850541)
    (by decide : 31850541 ≤ 31981613) S015C02.total S015C03.total

theorem join_0_2 : (twinPrimeSegment 31981613 32243757).card = 1179 := by
  simpa using combineTwinPrimeSegments (by decide : 31981613 ≤ 32112685)
    (by decide : 32112685 ≤ 32243757) S015C04.total S015C05.total

theorem join_0_3 : (twinPrimeSegment 32243757 32505901).card = 1099 := by
  simpa using combineTwinPrimeSegments (by decide : 32243757 ≤ 32374829)
    (by decide : 32374829 ≤ 32505901) S015C06.total S015C07.total

theorem join_0_4 : (twinPrimeSegment 32505901 32768045).card = 1122 := by
  simpa using combineTwinPrimeSegments (by decide : 32505901 ≤ 32636973)
    (by decide : 32636973 ≤ 32768045) S015C08.total S015C09.total

theorem join_0_5 : (twinPrimeSegment 32768045 33030189).card = 1156 := by
  simpa using combineTwinPrimeSegments (by decide : 32768045 ≤ 32899117)
    (by decide : 32899117 ≤ 33030189) S015C10.total S015C11.total

theorem join_0_6 : (twinPrimeSegment 33030189 33292333).card = 1171 := by
  simpa using combineTwinPrimeSegments (by decide : 33030189 ≤ 33161261)
    (by decide : 33161261 ≤ 33292333) S015C12.total S015C13.total

theorem join_0_7 : (twinPrimeSegment 33292333 33554477).card = 1167 := by
  simpa using combineTwinPrimeSegments (by decide : 33292333 ≤ 33423405)
    (by decide : 33423405 ≤ 33554477) S015C14.total S015C15.total

theorem join_1_0 : (twinPrimeSegment 31457325 31981613).card = 2336 := by
  simpa using combineTwinPrimeSegments (by decide : 31457325 ≤ 31719469)
    (by decide : 31719469 ≤ 31981613) join_0_0 join_0_1

theorem join_1_1 : (twinPrimeSegment 31981613 32505901).card = 2278 := by
  simpa using combineTwinPrimeSegments (by decide : 31981613 ≤ 32243757)
    (by decide : 32243757 ≤ 32505901) join_0_2 join_0_3

theorem join_1_2 : (twinPrimeSegment 32505901 33030189).card = 2278 := by
  simpa using combineTwinPrimeSegments (by decide : 32505901 ≤ 32768045)
    (by decide : 32768045 ≤ 33030189) join_0_4 join_0_5

theorem join_1_3 : (twinPrimeSegment 33030189 33554477).card = 2338 := by
  simpa using combineTwinPrimeSegments (by decide : 33030189 ≤ 33292333)
    (by decide : 33292333 ≤ 33554477) join_0_6 join_0_7

theorem join_2_0 : (twinPrimeSegment 31457325 32505901).card = 4614 := by
  simpa using combineTwinPrimeSegments (by decide : 31457325 ≤ 31981613)
    (by decide : 31981613 ≤ 32505901) join_1_0 join_1_1

theorem join_2_1 : (twinPrimeSegment 32505901 33554477).card = 4616 := by
  simpa using combineTwinPrimeSegments (by decide : 32505901 ≤ 33030189)
    (by decide : 33030189 ≤ 33554477) join_1_2 join_1_3

theorem join_3_0 : (twinPrimeSegment 31457325 33554477).card = 9230 := by
  simpa using combineTwinPrimeSegments (by decide : 31457325 ≤ 32505901)
    (by decide : 32505901 ≤ 33554477) join_2_0 join_2_1

theorem total : (twinPrimeSegment 31457325 33554477).card = 9230 := join_3_0

end S015All
end Sude.GeneratedTwinScan
