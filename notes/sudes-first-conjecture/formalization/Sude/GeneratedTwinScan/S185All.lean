import Sude.GeneratedTwinScan.S185C00
import Sude.GeneratedTwinScan.S185C01
import Sude.GeneratedTwinScan.S185C02
import Sude.GeneratedTwinScan.S185C03
import Sude.GeneratedTwinScan.S185C04
import Sude.GeneratedTwinScan.S185C05
import Sude.GeneratedTwinScan.S185C06
import Sude.GeneratedTwinScan.S185C07
import Sude.GeneratedTwinScan.S185C08
import Sude.GeneratedTwinScan.S185C09
import Sude.GeneratedTwinScan.S185C10
import Sude.GeneratedTwinScan.S185C11
import Sude.GeneratedTwinScan.S185C12
import Sude.GeneratedTwinScan.S185C13
import Sude.GeneratedTwinScan.S185C14
import Sude.GeneratedTwinScan.S185C15

/-! Combined FT source segment; Lean kernel check required. -/
namespace Sude.GeneratedTwinScan
namespace S185All

theorem join_0_0 : (twinPrimeSegment 387973165 388235309).card = 834 := by
  simpa using combineTwinPrimeSegments (by decide : 387973165 ≤ 388104237)
    (by decide : 388104237 ≤ 388235309) S185C00.total S185C01.total

theorem join_0_1 : (twinPrimeSegment 388235309 388497453).card = 902 := by
  simpa using combineTwinPrimeSegments (by decide : 388235309 ≤ 388366381)
    (by decide : 388366381 ≤ 388497453) S185C02.total S185C03.total

theorem join_0_2 : (twinPrimeSegment 388497453 388759597).card = 880 := by
  simpa using combineTwinPrimeSegments (by decide : 388497453 ≤ 388628525)
    (by decide : 388628525 ≤ 388759597) S185C04.total S185C05.total

theorem join_0_3 : (twinPrimeSegment 388759597 389021741).card = 903 := by
  simpa using combineTwinPrimeSegments (by decide : 388759597 ≤ 388890669)
    (by decide : 388890669 ≤ 389021741) S185C06.total S185C07.total

theorem join_0_4 : (twinPrimeSegment 389021741 389283885).card = 854 := by
  simpa using combineTwinPrimeSegments (by decide : 389021741 ≤ 389152813)
    (by decide : 389152813 ≤ 389283885) S185C08.total S185C09.total

theorem join_0_5 : (twinPrimeSegment 389283885 389546029).card = 887 := by
  simpa using combineTwinPrimeSegments (by decide : 389283885 ≤ 389414957)
    (by decide : 389414957 ≤ 389546029) S185C10.total S185C11.total

theorem join_0_6 : (twinPrimeSegment 389546029 389808173).card = 873 := by
  simpa using combineTwinPrimeSegments (by decide : 389546029 ≤ 389677101)
    (by decide : 389677101 ≤ 389808173) S185C12.total S185C13.total

theorem join_0_7 : (twinPrimeSegment 389808173 390070317).card = 869 := by
  simpa using combineTwinPrimeSegments (by decide : 389808173 ≤ 389939245)
    (by decide : 389939245 ≤ 390070317) S185C14.total S185C15.total

theorem join_1_0 : (twinPrimeSegment 387973165 388497453).card = 1736 := by
  simpa using combineTwinPrimeSegments (by decide : 387973165 ≤ 388235309)
    (by decide : 388235309 ≤ 388497453) join_0_0 join_0_1

theorem join_1_1 : (twinPrimeSegment 388497453 389021741).card = 1783 := by
  simpa using combineTwinPrimeSegments (by decide : 388497453 ≤ 388759597)
    (by decide : 388759597 ≤ 389021741) join_0_2 join_0_3

theorem join_1_2 : (twinPrimeSegment 389021741 389546029).card = 1741 := by
  simpa using combineTwinPrimeSegments (by decide : 389021741 ≤ 389283885)
    (by decide : 389283885 ≤ 389546029) join_0_4 join_0_5

theorem join_1_3 : (twinPrimeSegment 389546029 390070317).card = 1742 := by
  simpa using combineTwinPrimeSegments (by decide : 389546029 ≤ 389808173)
    (by decide : 389808173 ≤ 390070317) join_0_6 join_0_7

theorem join_2_0 : (twinPrimeSegment 387973165 389021741).card = 3519 := by
  simpa using combineTwinPrimeSegments (by decide : 387973165 ≤ 388497453)
    (by decide : 388497453 ≤ 389021741) join_1_0 join_1_1

theorem join_2_1 : (twinPrimeSegment 389021741 390070317).card = 3483 := by
  simpa using combineTwinPrimeSegments (by decide : 389021741 ≤ 389546029)
    (by decide : 389546029 ≤ 390070317) join_1_2 join_1_3

theorem join_3_0 : (twinPrimeSegment 387973165 390070317).card = 7002 := by
  simpa using combineTwinPrimeSegments (by decide : 387973165 ≤ 389021741)
    (by decide : 389021741 ≤ 390070317) join_2_0 join_2_1

theorem total : (twinPrimeSegment 387973165 390070317).card = 7002 := join_3_0

end S185All
end Sude.GeneratedTwinScan
