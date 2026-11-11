import Sude.GeneratedTwinScan.S131C00
import Sude.GeneratedTwinScan.S131C01
import Sude.GeneratedTwinScan.S131C02
import Sude.GeneratedTwinScan.S131C03
import Sude.GeneratedTwinScan.S131C04
import Sude.GeneratedTwinScan.S131C05
import Sude.GeneratedTwinScan.S131C06
import Sude.GeneratedTwinScan.S131C07
import Sude.GeneratedTwinScan.S131C08
import Sude.GeneratedTwinScan.S131C09
import Sude.GeneratedTwinScan.S131C10
import Sude.GeneratedTwinScan.S131C11
import Sude.GeneratedTwinScan.S131C12
import Sude.GeneratedTwinScan.S131C13
import Sude.GeneratedTwinScan.S131C14
import Sude.GeneratedTwinScan.S131C15

/-! Combined FT source segment; Lean kernel check required. -/
namespace Sude.GeneratedTwinScan
namespace S131All

theorem join_0_0 : (twinPrimeSegment 274726957 274989101).card = 878 := by
  simpa using combineTwinPrimeSegments (by decide : 274726957 ≤ 274858029)
    (by decide : 274858029 ≤ 274989101) S131C00.total S131C01.total

theorem join_0_1 : (twinPrimeSegment 274989101 275251245).card = 906 := by
  simpa using combineTwinPrimeSegments (by decide : 274989101 ≤ 275120173)
    (by decide : 275120173 ≤ 275251245) S131C02.total S131C03.total

theorem join_0_2 : (twinPrimeSegment 275251245 275513389).card = 906 := by
  simpa using combineTwinPrimeSegments (by decide : 275251245 ≤ 275382317)
    (by decide : 275382317 ≤ 275513389) S131C04.total S131C05.total

theorem join_0_3 : (twinPrimeSegment 275513389 275775533).card = 890 := by
  simpa using combineTwinPrimeSegments (by decide : 275513389 ≤ 275644461)
    (by decide : 275644461 ≤ 275775533) S131C06.total S131C07.total

theorem join_0_4 : (twinPrimeSegment 275775533 276037677).card = 952 := by
  simpa using combineTwinPrimeSegments (by decide : 275775533 ≤ 275906605)
    (by decide : 275906605 ≤ 276037677) S131C08.total S131C09.total

theorem join_0_5 : (twinPrimeSegment 276037677 276299821).card = 916 := by
  simpa using combineTwinPrimeSegments (by decide : 276037677 ≤ 276168749)
    (by decide : 276168749 ≤ 276299821) S131C10.total S131C11.total

theorem join_0_6 : (twinPrimeSegment 276299821 276561965).card = 901 := by
  simpa using combineTwinPrimeSegments (by decide : 276299821 ≤ 276430893)
    (by decide : 276430893 ≤ 276561965) S131C12.total S131C13.total

theorem join_0_7 : (twinPrimeSegment 276561965 276824109).card = 950 := by
  simpa using combineTwinPrimeSegments (by decide : 276561965 ≤ 276693037)
    (by decide : 276693037 ≤ 276824109) S131C14.total S131C15.total

theorem join_1_0 : (twinPrimeSegment 274726957 275251245).card = 1784 := by
  simpa using combineTwinPrimeSegments (by decide : 274726957 ≤ 274989101)
    (by decide : 274989101 ≤ 275251245) join_0_0 join_0_1

theorem join_1_1 : (twinPrimeSegment 275251245 275775533).card = 1796 := by
  simpa using combineTwinPrimeSegments (by decide : 275251245 ≤ 275513389)
    (by decide : 275513389 ≤ 275775533) join_0_2 join_0_3

theorem join_1_2 : (twinPrimeSegment 275775533 276299821).card = 1868 := by
  simpa using combineTwinPrimeSegments (by decide : 275775533 ≤ 276037677)
    (by decide : 276037677 ≤ 276299821) join_0_4 join_0_5

theorem join_1_3 : (twinPrimeSegment 276299821 276824109).card = 1851 := by
  simpa using combineTwinPrimeSegments (by decide : 276299821 ≤ 276561965)
    (by decide : 276561965 ≤ 276824109) join_0_6 join_0_7

theorem join_2_0 : (twinPrimeSegment 274726957 275775533).card = 3580 := by
  simpa using combineTwinPrimeSegments (by decide : 274726957 ≤ 275251245)
    (by decide : 275251245 ≤ 275775533) join_1_0 join_1_1

theorem join_2_1 : (twinPrimeSegment 275775533 276824109).card = 3719 := by
  simpa using combineTwinPrimeSegments (by decide : 275775533 ≤ 276299821)
    (by decide : 276299821 ≤ 276824109) join_1_2 join_1_3

theorem join_3_0 : (twinPrimeSegment 274726957 276824109).card = 7299 := by
  simpa using combineTwinPrimeSegments (by decide : 274726957 ≤ 275775533)
    (by decide : 275775533 ≤ 276824109) join_2_0 join_2_1

theorem total : (twinPrimeSegment 274726957 276824109).card = 7299 := join_3_0

end S131All
end Sude.GeneratedTwinScan
