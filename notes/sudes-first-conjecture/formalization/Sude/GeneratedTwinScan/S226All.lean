import Sude.GeneratedTwinScan.S226C00
import Sude.GeneratedTwinScan.S226C01
import Sude.GeneratedTwinScan.S226C02
import Sude.GeneratedTwinScan.S226C03
import Sude.GeneratedTwinScan.S226C04
import Sude.GeneratedTwinScan.S226C05
import Sude.GeneratedTwinScan.S226C06
import Sude.GeneratedTwinScan.S226C07
import Sude.GeneratedTwinScan.S226C08
import Sude.GeneratedTwinScan.S226C09
import Sude.GeneratedTwinScan.S226C10
import Sude.GeneratedTwinScan.S226C11
import Sude.GeneratedTwinScan.S226C12
import Sude.GeneratedTwinScan.S226C13
import Sude.GeneratedTwinScan.S226C14
import Sude.GeneratedTwinScan.S226C15

/-! Combined FT source segment; Lean kernel check required. -/
namespace Sude.GeneratedTwinScan
namespace S226All

theorem join_0_0 : (twinPrimeSegment 473956397 474218541).card = 864 := by
  simpa using combineTwinPrimeSegments (by decide : 473956397 ≤ 474087469)
    (by decide : 474087469 ≤ 474218541) S226C00.total S226C01.total

theorem join_0_1 : (twinPrimeSegment 474218541 474480685).card = 824 := by
  simpa using combineTwinPrimeSegments (by decide : 474218541 ≤ 474349613)
    (by decide : 474349613 ≤ 474480685) S226C02.total S226C03.total

theorem join_0_2 : (twinPrimeSegment 474480685 474742829).card = 875 := by
  simpa using combineTwinPrimeSegments (by decide : 474480685 ≤ 474611757)
    (by decide : 474611757 ≤ 474742829) S226C04.total S226C05.total

theorem join_0_3 : (twinPrimeSegment 474742829 475004973).card = 881 := by
  simpa using combineTwinPrimeSegments (by decide : 474742829 ≤ 474873901)
    (by decide : 474873901 ≤ 475004973) S226C06.total S226C07.total

theorem join_0_4 : (twinPrimeSegment 475004973 475267117).card = 866 := by
  simpa using combineTwinPrimeSegments (by decide : 475004973 ≤ 475136045)
    (by decide : 475136045 ≤ 475267117) S226C08.total S226C09.total

theorem join_0_5 : (twinPrimeSegment 475267117 475529261).card = 861 := by
  simpa using combineTwinPrimeSegments (by decide : 475267117 ≤ 475398189)
    (by decide : 475398189 ≤ 475529261) S226C10.total S226C11.total

theorem join_0_6 : (twinPrimeSegment 475529261 475791405).card = 920 := by
  simpa using combineTwinPrimeSegments (by decide : 475529261 ≤ 475660333)
    (by decide : 475660333 ≤ 475791405) S226C12.total S226C13.total

theorem join_0_7 : (twinPrimeSegment 475791405 476053549).card = 849 := by
  simpa using combineTwinPrimeSegments (by decide : 475791405 ≤ 475922477)
    (by decide : 475922477 ≤ 476053549) S226C14.total S226C15.total

theorem join_1_0 : (twinPrimeSegment 473956397 474480685).card = 1688 := by
  simpa using combineTwinPrimeSegments (by decide : 473956397 ≤ 474218541)
    (by decide : 474218541 ≤ 474480685) join_0_0 join_0_1

theorem join_1_1 : (twinPrimeSegment 474480685 475004973).card = 1756 := by
  simpa using combineTwinPrimeSegments (by decide : 474480685 ≤ 474742829)
    (by decide : 474742829 ≤ 475004973) join_0_2 join_0_3

theorem join_1_2 : (twinPrimeSegment 475004973 475529261).card = 1727 := by
  simpa using combineTwinPrimeSegments (by decide : 475004973 ≤ 475267117)
    (by decide : 475267117 ≤ 475529261) join_0_4 join_0_5

theorem join_1_3 : (twinPrimeSegment 475529261 476053549).card = 1769 := by
  simpa using combineTwinPrimeSegments (by decide : 475529261 ≤ 475791405)
    (by decide : 475791405 ≤ 476053549) join_0_6 join_0_7

theorem join_2_0 : (twinPrimeSegment 473956397 475004973).card = 3444 := by
  simpa using combineTwinPrimeSegments (by decide : 473956397 ≤ 474480685)
    (by decide : 474480685 ≤ 475004973) join_1_0 join_1_1

theorem join_2_1 : (twinPrimeSegment 475004973 476053549).card = 3496 := by
  simpa using combineTwinPrimeSegments (by decide : 475004973 ≤ 475529261)
    (by decide : 475529261 ≤ 476053549) join_1_2 join_1_3

theorem join_3_0 : (twinPrimeSegment 473956397 476053549).card = 6940 := by
  simpa using combineTwinPrimeSegments (by decide : 473956397 ≤ 475004973)
    (by decide : 475004973 ≤ 476053549) join_2_0 join_2_1

theorem total : (twinPrimeSegment 473956397 476053549).card = 6940 := join_3_0

end S226All
end Sude.GeneratedTwinScan
