import Sude.GeneratedTwinScan.S179C00
import Sude.GeneratedTwinScan.S179C01
import Sude.GeneratedTwinScan.S179C02
import Sude.GeneratedTwinScan.S179C03
import Sude.GeneratedTwinScan.S179C04
import Sude.GeneratedTwinScan.S179C05
import Sude.GeneratedTwinScan.S179C06
import Sude.GeneratedTwinScan.S179C07
import Sude.GeneratedTwinScan.S179C08
import Sude.GeneratedTwinScan.S179C09
import Sude.GeneratedTwinScan.S179C10
import Sude.GeneratedTwinScan.S179C11
import Sude.GeneratedTwinScan.S179C12
import Sude.GeneratedTwinScan.S179C13
import Sude.GeneratedTwinScan.S179C14
import Sude.GeneratedTwinScan.S179C15

/-! Combined FT source segment; Lean kernel check required. -/
namespace Sude.GeneratedTwinScan
namespace S179All

theorem join_0_0 : (twinPrimeSegment 375390253 375652397).card = 922 := by
  simpa using combineTwinPrimeSegments (by decide : 375390253 ≤ 375521325)
    (by decide : 375521325 ≤ 375652397) S179C00.total S179C01.total

theorem join_0_1 : (twinPrimeSegment 375652397 375914541).card = 871 := by
  simpa using combineTwinPrimeSegments (by decide : 375652397 ≤ 375783469)
    (by decide : 375783469 ≤ 375914541) S179C02.total S179C03.total

theorem join_0_2 : (twinPrimeSegment 375914541 376176685).card = 866 := by
  simpa using combineTwinPrimeSegments (by decide : 375914541 ≤ 376045613)
    (by decide : 376045613 ≤ 376176685) S179C04.total S179C05.total

theorem join_0_3 : (twinPrimeSegment 376176685 376438829).card = 885 := by
  simpa using combineTwinPrimeSegments (by decide : 376176685 ≤ 376307757)
    (by decide : 376307757 ≤ 376438829) S179C06.total S179C07.total

theorem join_0_4 : (twinPrimeSegment 376438829 376700973).card = 871 := by
  simpa using combineTwinPrimeSegments (by decide : 376438829 ≤ 376569901)
    (by decide : 376569901 ≤ 376700973) S179C08.total S179C09.total

theorem join_0_5 : (twinPrimeSegment 376700973 376963117).card = 872 := by
  simpa using combineTwinPrimeSegments (by decide : 376700973 ≤ 376832045)
    (by decide : 376832045 ≤ 376963117) S179C10.total S179C11.total

theorem join_0_6 : (twinPrimeSegment 376963117 377225261).card = 885 := by
  simpa using combineTwinPrimeSegments (by decide : 376963117 ≤ 377094189)
    (by decide : 377094189 ≤ 377225261) S179C12.total S179C13.total

theorem join_0_7 : (twinPrimeSegment 377225261 377487405).card = 907 := by
  simpa using combineTwinPrimeSegments (by decide : 377225261 ≤ 377356333)
    (by decide : 377356333 ≤ 377487405) S179C14.total S179C15.total

theorem join_1_0 : (twinPrimeSegment 375390253 375914541).card = 1793 := by
  simpa using combineTwinPrimeSegments (by decide : 375390253 ≤ 375652397)
    (by decide : 375652397 ≤ 375914541) join_0_0 join_0_1

theorem join_1_1 : (twinPrimeSegment 375914541 376438829).card = 1751 := by
  simpa using combineTwinPrimeSegments (by decide : 375914541 ≤ 376176685)
    (by decide : 376176685 ≤ 376438829) join_0_2 join_0_3

theorem join_1_2 : (twinPrimeSegment 376438829 376963117).card = 1743 := by
  simpa using combineTwinPrimeSegments (by decide : 376438829 ≤ 376700973)
    (by decide : 376700973 ≤ 376963117) join_0_4 join_0_5

theorem join_1_3 : (twinPrimeSegment 376963117 377487405).card = 1792 := by
  simpa using combineTwinPrimeSegments (by decide : 376963117 ≤ 377225261)
    (by decide : 377225261 ≤ 377487405) join_0_6 join_0_7

theorem join_2_0 : (twinPrimeSegment 375390253 376438829).card = 3544 := by
  simpa using combineTwinPrimeSegments (by decide : 375390253 ≤ 375914541)
    (by decide : 375914541 ≤ 376438829) join_1_0 join_1_1

theorem join_2_1 : (twinPrimeSegment 376438829 377487405).card = 3535 := by
  simpa using combineTwinPrimeSegments (by decide : 376438829 ≤ 376963117)
    (by decide : 376963117 ≤ 377487405) join_1_2 join_1_3

theorem join_3_0 : (twinPrimeSegment 375390253 377487405).card = 7079 := by
  simpa using combineTwinPrimeSegments (by decide : 375390253 ≤ 376438829)
    (by decide : 376438829 ≤ 377487405) join_2_0 join_2_1

theorem total : (twinPrimeSegment 375390253 377487405).card = 7079 := join_3_0

end S179All
end Sude.GeneratedTwinScan
