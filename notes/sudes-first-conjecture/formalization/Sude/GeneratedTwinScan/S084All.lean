import Sude.GeneratedTwinScan.S084C00
import Sude.GeneratedTwinScan.S084C01
import Sude.GeneratedTwinScan.S084C02
import Sude.GeneratedTwinScan.S084C03
import Sude.GeneratedTwinScan.S084C04
import Sude.GeneratedTwinScan.S084C05
import Sude.GeneratedTwinScan.S084C06
import Sude.GeneratedTwinScan.S084C07
import Sude.GeneratedTwinScan.S084C08
import Sude.GeneratedTwinScan.S084C09
import Sude.GeneratedTwinScan.S084C10
import Sude.GeneratedTwinScan.S084C11
import Sude.GeneratedTwinScan.S084C12
import Sude.GeneratedTwinScan.S084C13
import Sude.GeneratedTwinScan.S084C14
import Sude.GeneratedTwinScan.S084C15

/-! Combined FT source segment; Lean kernel check required. -/
namespace Sude.GeneratedTwinScan
namespace S084All

theorem join_0_0 : (twinPrimeSegment 176160813 176422957).card = 919 := by
  simpa using combineTwinPrimeSegments (by decide : 176160813 ≤ 176291885)
    (by decide : 176291885 ≤ 176422957) S084C00.total S084C01.total

theorem join_0_1 : (twinPrimeSegment 176422957 176685101).card = 957 := by
  simpa using combineTwinPrimeSegments (by decide : 176422957 ≤ 176554029)
    (by decide : 176554029 ≤ 176685101) S084C02.total S084C03.total

theorem join_0_2 : (twinPrimeSegment 176685101 176947245).card = 989 := by
  simpa using combineTwinPrimeSegments (by decide : 176685101 ≤ 176816173)
    (by decide : 176816173 ≤ 176947245) S084C04.total S084C05.total

theorem join_0_3 : (twinPrimeSegment 176947245 177209389).card = 959 := by
  simpa using combineTwinPrimeSegments (by decide : 176947245 ≤ 177078317)
    (by decide : 177078317 ≤ 177209389) S084C06.total S084C07.total

theorem join_0_4 : (twinPrimeSegment 177209389 177471533).card = 972 := by
  simpa using combineTwinPrimeSegments (by decide : 177209389 ≤ 177340461)
    (by decide : 177340461 ≤ 177471533) S084C08.total S084C09.total

theorem join_0_5 : (twinPrimeSegment 177471533 177733677).card = 958 := by
  simpa using combineTwinPrimeSegments (by decide : 177471533 ≤ 177602605)
    (by decide : 177602605 ≤ 177733677) S084C10.total S084C11.total

theorem join_0_6 : (twinPrimeSegment 177733677 177995821).card = 962 := by
  simpa using combineTwinPrimeSegments (by decide : 177733677 ≤ 177864749)
    (by decide : 177864749 ≤ 177995821) S084C12.total S084C13.total

theorem join_0_7 : (twinPrimeSegment 177995821 178257965).card = 964 := by
  simpa using combineTwinPrimeSegments (by decide : 177995821 ≤ 178126893)
    (by decide : 178126893 ≤ 178257965) S084C14.total S084C15.total

theorem join_1_0 : (twinPrimeSegment 176160813 176685101).card = 1876 := by
  simpa using combineTwinPrimeSegments (by decide : 176160813 ≤ 176422957)
    (by decide : 176422957 ≤ 176685101) join_0_0 join_0_1

theorem join_1_1 : (twinPrimeSegment 176685101 177209389).card = 1948 := by
  simpa using combineTwinPrimeSegments (by decide : 176685101 ≤ 176947245)
    (by decide : 176947245 ≤ 177209389) join_0_2 join_0_3

theorem join_1_2 : (twinPrimeSegment 177209389 177733677).card = 1930 := by
  simpa using combineTwinPrimeSegments (by decide : 177209389 ≤ 177471533)
    (by decide : 177471533 ≤ 177733677) join_0_4 join_0_5

theorem join_1_3 : (twinPrimeSegment 177733677 178257965).card = 1926 := by
  simpa using combineTwinPrimeSegments (by decide : 177733677 ≤ 177995821)
    (by decide : 177995821 ≤ 178257965) join_0_6 join_0_7

theorem join_2_0 : (twinPrimeSegment 176160813 177209389).card = 3824 := by
  simpa using combineTwinPrimeSegments (by decide : 176160813 ≤ 176685101)
    (by decide : 176685101 ≤ 177209389) join_1_0 join_1_1

theorem join_2_1 : (twinPrimeSegment 177209389 178257965).card = 3856 := by
  simpa using combineTwinPrimeSegments (by decide : 177209389 ≤ 177733677)
    (by decide : 177733677 ≤ 178257965) join_1_2 join_1_3

theorem join_3_0 : (twinPrimeSegment 176160813 178257965).card = 7680 := by
  simpa using combineTwinPrimeSegments (by decide : 176160813 ≤ 177209389)
    (by decide : 177209389 ≤ 178257965) join_2_0 join_2_1

theorem total : (twinPrimeSegment 176160813 178257965).card = 7680 := join_3_0

end S084All
end Sude.GeneratedTwinScan
