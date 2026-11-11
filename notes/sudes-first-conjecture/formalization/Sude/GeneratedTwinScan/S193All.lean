import Sude.GeneratedTwinScan.S193C00
import Sude.GeneratedTwinScan.S193C01
import Sude.GeneratedTwinScan.S193C02
import Sude.GeneratedTwinScan.S193C03
import Sude.GeneratedTwinScan.S193C04
import Sude.GeneratedTwinScan.S193C05
import Sude.GeneratedTwinScan.S193C06
import Sude.GeneratedTwinScan.S193C07
import Sude.GeneratedTwinScan.S193C08
import Sude.GeneratedTwinScan.S193C09
import Sude.GeneratedTwinScan.S193C10
import Sude.GeneratedTwinScan.S193C11
import Sude.GeneratedTwinScan.S193C12
import Sude.GeneratedTwinScan.S193C13
import Sude.GeneratedTwinScan.S193C14
import Sude.GeneratedTwinScan.S193C15

/-! Combined FT source segment; Lean kernel check required. -/
namespace Sude.GeneratedTwinScan
namespace S193All

theorem join_0_0 : (twinPrimeSegment 404750381 405012525).card = 873 := by
  simpa using combineTwinPrimeSegments (by decide : 404750381 ≤ 404881453)
    (by decide : 404881453 ≤ 405012525) S193C00.total S193C01.total

theorem join_0_1 : (twinPrimeSegment 405012525 405274669).card = 877 := by
  simpa using combineTwinPrimeSegments (by decide : 405012525 ≤ 405143597)
    (by decide : 405143597 ≤ 405274669) S193C02.total S193C03.total

theorem join_0_2 : (twinPrimeSegment 405274669 405536813).card = 852 := by
  simpa using combineTwinPrimeSegments (by decide : 405274669 ≤ 405405741)
    (by decide : 405405741 ≤ 405536813) S193C04.total S193C05.total

theorem join_0_3 : (twinPrimeSegment 405536813 405798957).card = 876 := by
  simpa using combineTwinPrimeSegments (by decide : 405536813 ≤ 405667885)
    (by decide : 405667885 ≤ 405798957) S193C06.total S193C07.total

theorem join_0_4 : (twinPrimeSegment 405798957 406061101).card = 895 := by
  simpa using combineTwinPrimeSegments (by decide : 405798957 ≤ 405930029)
    (by decide : 405930029 ≤ 406061101) S193C08.total S193C09.total

theorem join_0_5 : (twinPrimeSegment 406061101 406323245).card = 871 := by
  simpa using combineTwinPrimeSegments (by decide : 406061101 ≤ 406192173)
    (by decide : 406192173 ≤ 406323245) S193C10.total S193C11.total

theorem join_0_6 : (twinPrimeSegment 406323245 406585389).card = 874 := by
  simpa using combineTwinPrimeSegments (by decide : 406323245 ≤ 406454317)
    (by decide : 406454317 ≤ 406585389) S193C12.total S193C13.total

theorem join_0_7 : (twinPrimeSegment 406585389 406847533).card = 878 := by
  simpa using combineTwinPrimeSegments (by decide : 406585389 ≤ 406716461)
    (by decide : 406716461 ≤ 406847533) S193C14.total S193C15.total

theorem join_1_0 : (twinPrimeSegment 404750381 405274669).card = 1750 := by
  simpa using combineTwinPrimeSegments (by decide : 404750381 ≤ 405012525)
    (by decide : 405012525 ≤ 405274669) join_0_0 join_0_1

theorem join_1_1 : (twinPrimeSegment 405274669 405798957).card = 1728 := by
  simpa using combineTwinPrimeSegments (by decide : 405274669 ≤ 405536813)
    (by decide : 405536813 ≤ 405798957) join_0_2 join_0_3

theorem join_1_2 : (twinPrimeSegment 405798957 406323245).card = 1766 := by
  simpa using combineTwinPrimeSegments (by decide : 405798957 ≤ 406061101)
    (by decide : 406061101 ≤ 406323245) join_0_4 join_0_5

theorem join_1_3 : (twinPrimeSegment 406323245 406847533).card = 1752 := by
  simpa using combineTwinPrimeSegments (by decide : 406323245 ≤ 406585389)
    (by decide : 406585389 ≤ 406847533) join_0_6 join_0_7

theorem join_2_0 : (twinPrimeSegment 404750381 405798957).card = 3478 := by
  simpa using combineTwinPrimeSegments (by decide : 404750381 ≤ 405274669)
    (by decide : 405274669 ≤ 405798957) join_1_0 join_1_1

theorem join_2_1 : (twinPrimeSegment 405798957 406847533).card = 3518 := by
  simpa using combineTwinPrimeSegments (by decide : 405798957 ≤ 406323245)
    (by decide : 406323245 ≤ 406847533) join_1_2 join_1_3

theorem join_3_0 : (twinPrimeSegment 404750381 406847533).card = 6996 := by
  simpa using combineTwinPrimeSegments (by decide : 404750381 ≤ 405798957)
    (by decide : 405798957 ≤ 406847533) join_2_0 join_2_1

theorem total : (twinPrimeSegment 404750381 406847533).card = 6996 := join_3_0

end S193All
end Sude.GeneratedTwinScan
