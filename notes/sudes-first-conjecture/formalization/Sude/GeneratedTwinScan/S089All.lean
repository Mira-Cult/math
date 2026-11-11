import Sude.GeneratedTwinScan.S089C00
import Sude.GeneratedTwinScan.S089C01
import Sude.GeneratedTwinScan.S089C02
import Sude.GeneratedTwinScan.S089C03
import Sude.GeneratedTwinScan.S089C04
import Sude.GeneratedTwinScan.S089C05
import Sude.GeneratedTwinScan.S089C06
import Sude.GeneratedTwinScan.S089C07
import Sude.GeneratedTwinScan.S089C08
import Sude.GeneratedTwinScan.S089C09
import Sude.GeneratedTwinScan.S089C10
import Sude.GeneratedTwinScan.S089C11
import Sude.GeneratedTwinScan.S089C12
import Sude.GeneratedTwinScan.S089C13
import Sude.GeneratedTwinScan.S089C14
import Sude.GeneratedTwinScan.S089C15

/-! Combined FT source segment; Lean kernel check required. -/
namespace Sude.GeneratedTwinScan
namespace S089All

theorem join_0_0 : (twinPrimeSegment 186646573 186908717).card = 954 := by
  simpa using combineTwinPrimeSegments (by decide : 186646573 ≤ 186777645)
    (by decide : 186777645 ≤ 186908717) S089C00.total S089C01.total

theorem join_0_1 : (twinPrimeSegment 186908717 187170861).card = 990 := by
  simpa using combineTwinPrimeSegments (by decide : 186908717 ≤ 187039789)
    (by decide : 187039789 ≤ 187170861) S089C02.total S089C03.total

theorem join_0_2 : (twinPrimeSegment 187170861 187433005).card = 1001 := by
  simpa using combineTwinPrimeSegments (by decide : 187170861 ≤ 187301933)
    (by decide : 187301933 ≤ 187433005) S089C04.total S089C05.total

theorem join_0_3 : (twinPrimeSegment 187433005 187695149).card = 918 := by
  simpa using combineTwinPrimeSegments (by decide : 187433005 ≤ 187564077)
    (by decide : 187564077 ≤ 187695149) S089C06.total S089C07.total

theorem join_0_4 : (twinPrimeSegment 187695149 187957293).card = 1020 := by
  simpa using combineTwinPrimeSegments (by decide : 187695149 ≤ 187826221)
    (by decide : 187826221 ≤ 187957293) S089C08.total S089C09.total

theorem join_0_5 : (twinPrimeSegment 187957293 188219437).card = 962 := by
  simpa using combineTwinPrimeSegments (by decide : 187957293 ≤ 188088365)
    (by decide : 188088365 ≤ 188219437) S089C10.total S089C11.total

theorem join_0_6 : (twinPrimeSegment 188219437 188481581).card = 941 := by
  simpa using combineTwinPrimeSegments (by decide : 188219437 ≤ 188350509)
    (by decide : 188350509 ≤ 188481581) S089C12.total S089C13.total

theorem join_0_7 : (twinPrimeSegment 188481581 188743725).card = 916 := by
  simpa using combineTwinPrimeSegments (by decide : 188481581 ≤ 188612653)
    (by decide : 188612653 ≤ 188743725) S089C14.total S089C15.total

theorem join_1_0 : (twinPrimeSegment 186646573 187170861).card = 1944 := by
  simpa using combineTwinPrimeSegments (by decide : 186646573 ≤ 186908717)
    (by decide : 186908717 ≤ 187170861) join_0_0 join_0_1

theorem join_1_1 : (twinPrimeSegment 187170861 187695149).card = 1919 := by
  simpa using combineTwinPrimeSegments (by decide : 187170861 ≤ 187433005)
    (by decide : 187433005 ≤ 187695149) join_0_2 join_0_3

theorem join_1_2 : (twinPrimeSegment 187695149 188219437).card = 1982 := by
  simpa using combineTwinPrimeSegments (by decide : 187695149 ≤ 187957293)
    (by decide : 187957293 ≤ 188219437) join_0_4 join_0_5

theorem join_1_3 : (twinPrimeSegment 188219437 188743725).card = 1857 := by
  simpa using combineTwinPrimeSegments (by decide : 188219437 ≤ 188481581)
    (by decide : 188481581 ≤ 188743725) join_0_6 join_0_7

theorem join_2_0 : (twinPrimeSegment 186646573 187695149).card = 3863 := by
  simpa using combineTwinPrimeSegments (by decide : 186646573 ≤ 187170861)
    (by decide : 187170861 ≤ 187695149) join_1_0 join_1_1

theorem join_2_1 : (twinPrimeSegment 187695149 188743725).card = 3839 := by
  simpa using combineTwinPrimeSegments (by decide : 187695149 ≤ 188219437)
    (by decide : 188219437 ≤ 188743725) join_1_2 join_1_3

theorem join_3_0 : (twinPrimeSegment 186646573 188743725).card = 7702 := by
  simpa using combineTwinPrimeSegments (by decide : 186646573 ≤ 187695149)
    (by decide : 187695149 ≤ 188743725) join_2_0 join_2_1

theorem total : (twinPrimeSegment 186646573 188743725).card = 7702 := join_3_0

end S089All
end Sude.GeneratedTwinScan
