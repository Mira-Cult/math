import Sude.GeneratedTwinScan.S010C00
import Sude.GeneratedTwinScan.S010C01
import Sude.GeneratedTwinScan.S010C02
import Sude.GeneratedTwinScan.S010C03
import Sude.GeneratedTwinScan.S010C04
import Sude.GeneratedTwinScan.S010C05
import Sude.GeneratedTwinScan.S010C06
import Sude.GeneratedTwinScan.S010C07
import Sude.GeneratedTwinScan.S010C08
import Sude.GeneratedTwinScan.S010C09
import Sude.GeneratedTwinScan.S010C10
import Sude.GeneratedTwinScan.S010C11
import Sude.GeneratedTwinScan.S010C12
import Sude.GeneratedTwinScan.S010C13
import Sude.GeneratedTwinScan.S010C14
import Sude.GeneratedTwinScan.S010C15

/-! Combined FT source segment; Lean kernel check required. -/
namespace Sude.GeneratedTwinScan
namespace S010All

theorem join_0_0 : (twinPrimeSegment 20971565 21233709).card = 1219 := by
  simpa using combineTwinPrimeSegments (by decide : 20971565 ≤ 21102637)
    (by decide : 21102637 ≤ 21233709) S010C00.total S010C01.total

theorem join_0_1 : (twinPrimeSegment 21233709 21495853).card = 1223 := by
  simpa using combineTwinPrimeSegments (by decide : 21233709 ≤ 21364781)
    (by decide : 21364781 ≤ 21495853) S010C02.total S010C03.total

theorem join_0_2 : (twinPrimeSegment 21495853 21757997).card = 1197 := by
  simpa using combineTwinPrimeSegments (by decide : 21495853 ≤ 21626925)
    (by decide : 21626925 ≤ 21757997) S010C04.total S010C05.total

theorem join_0_3 : (twinPrimeSegment 21757997 22020141).card = 1182 := by
  simpa using combineTwinPrimeSegments (by decide : 21757997 ≤ 21889069)
    (by decide : 21889069 ≤ 22020141) S010C06.total S010C07.total

theorem join_0_4 : (twinPrimeSegment 22020141 22282285).card = 1179 := by
  simpa using combineTwinPrimeSegments (by decide : 22020141 ≤ 22151213)
    (by decide : 22151213 ≤ 22282285) S010C08.total S010C09.total

theorem join_0_5 : (twinPrimeSegment 22282285 22544429).card = 1216 := by
  simpa using combineTwinPrimeSegments (by decide : 22282285 ≤ 22413357)
    (by decide : 22413357 ≤ 22544429) S010C10.total S010C11.total

theorem join_0_6 : (twinPrimeSegment 22544429 22806573).card = 1221 := by
  simpa using combineTwinPrimeSegments (by decide : 22544429 ≤ 22675501)
    (by decide : 22675501 ≤ 22806573) S010C12.total S010C13.total

theorem join_0_7 : (twinPrimeSegment 22806573 23068717).card = 1224 := by
  simpa using combineTwinPrimeSegments (by decide : 22806573 ≤ 22937645)
    (by decide : 22937645 ≤ 23068717) S010C14.total S010C15.total

theorem join_1_0 : (twinPrimeSegment 20971565 21495853).card = 2442 := by
  simpa using combineTwinPrimeSegments (by decide : 20971565 ≤ 21233709)
    (by decide : 21233709 ≤ 21495853) join_0_0 join_0_1

theorem join_1_1 : (twinPrimeSegment 21495853 22020141).card = 2379 := by
  simpa using combineTwinPrimeSegments (by decide : 21495853 ≤ 21757997)
    (by decide : 21757997 ≤ 22020141) join_0_2 join_0_3

theorem join_1_2 : (twinPrimeSegment 22020141 22544429).card = 2395 := by
  simpa using combineTwinPrimeSegments (by decide : 22020141 ≤ 22282285)
    (by decide : 22282285 ≤ 22544429) join_0_4 join_0_5

theorem join_1_3 : (twinPrimeSegment 22544429 23068717).card = 2445 := by
  simpa using combineTwinPrimeSegments (by decide : 22544429 ≤ 22806573)
    (by decide : 22806573 ≤ 23068717) join_0_6 join_0_7

theorem join_2_0 : (twinPrimeSegment 20971565 22020141).card = 4821 := by
  simpa using combineTwinPrimeSegments (by decide : 20971565 ≤ 21495853)
    (by decide : 21495853 ≤ 22020141) join_1_0 join_1_1

theorem join_2_1 : (twinPrimeSegment 22020141 23068717).card = 4840 := by
  simpa using combineTwinPrimeSegments (by decide : 22020141 ≤ 22544429)
    (by decide : 22544429 ≤ 23068717) join_1_2 join_1_3

theorem join_3_0 : (twinPrimeSegment 20971565 23068717).card = 9661 := by
  simpa using combineTwinPrimeSegments (by decide : 20971565 ≤ 22020141)
    (by decide : 22020141 ≤ 23068717) join_2_0 join_2_1

theorem total : (twinPrimeSegment 20971565 23068717).card = 9661 := join_3_0

end S010All
end Sude.GeneratedTwinScan
