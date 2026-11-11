import Sude.GeneratedTwinScan.S219C00
import Sude.GeneratedTwinScan.S219C01
import Sude.GeneratedTwinScan.S219C02
import Sude.GeneratedTwinScan.S219C03
import Sude.GeneratedTwinScan.S219C04
import Sude.GeneratedTwinScan.S219C05
import Sude.GeneratedTwinScan.S219C06
import Sude.GeneratedTwinScan.S219C07
import Sude.GeneratedTwinScan.S219C08
import Sude.GeneratedTwinScan.S219C09
import Sude.GeneratedTwinScan.S219C10
import Sude.GeneratedTwinScan.S219C11
import Sude.GeneratedTwinScan.S219C12
import Sude.GeneratedTwinScan.S219C13
import Sude.GeneratedTwinScan.S219C14
import Sude.GeneratedTwinScan.S219C15

/-! Combined FT source segment; Lean kernel check required. -/
namespace Sude.GeneratedTwinScan
namespace S219All

theorem join_0_0 : (twinPrimeSegment 459276333 459538477).card = 836 := by
  simpa using combineTwinPrimeSegments (by decide : 459276333 ≤ 459407405)
    (by decide : 459407405 ≤ 459538477) S219C00.total S219C01.total

theorem join_0_1 : (twinPrimeSegment 459538477 459800621).card = 879 := by
  simpa using combineTwinPrimeSegments (by decide : 459538477 ≤ 459669549)
    (by decide : 459669549 ≤ 459800621) S219C02.total S219C03.total

theorem join_0_2 : (twinPrimeSegment 459800621 460062765).card = 919 := by
  simpa using combineTwinPrimeSegments (by decide : 459800621 ≤ 459931693)
    (by decide : 459931693 ≤ 460062765) S219C04.total S219C05.total

theorem join_0_3 : (twinPrimeSegment 460062765 460324909).card = 831 := by
  simpa using combineTwinPrimeSegments (by decide : 460062765 ≤ 460193837)
    (by decide : 460193837 ≤ 460324909) S219C06.total S219C07.total

theorem join_0_4 : (twinPrimeSegment 460324909 460587053).card = 857 := by
  simpa using combineTwinPrimeSegments (by decide : 460324909 ≤ 460455981)
    (by decide : 460455981 ≤ 460587053) S219C08.total S219C09.total

theorem join_0_5 : (twinPrimeSegment 460587053 460849197).card = 866 := by
  simpa using combineTwinPrimeSegments (by decide : 460587053 ≤ 460718125)
    (by decide : 460718125 ≤ 460849197) S219C10.total S219C11.total

theorem join_0_6 : (twinPrimeSegment 460849197 461111341).card = 861 := by
  simpa using combineTwinPrimeSegments (by decide : 460849197 ≤ 460980269)
    (by decide : 460980269 ≤ 461111341) S219C12.total S219C13.total

theorem join_0_7 : (twinPrimeSegment 461111341 461373485).card = 867 := by
  simpa using combineTwinPrimeSegments (by decide : 461111341 ≤ 461242413)
    (by decide : 461242413 ≤ 461373485) S219C14.total S219C15.total

theorem join_1_0 : (twinPrimeSegment 459276333 459800621).card = 1715 := by
  simpa using combineTwinPrimeSegments (by decide : 459276333 ≤ 459538477)
    (by decide : 459538477 ≤ 459800621) join_0_0 join_0_1

theorem join_1_1 : (twinPrimeSegment 459800621 460324909).card = 1750 := by
  simpa using combineTwinPrimeSegments (by decide : 459800621 ≤ 460062765)
    (by decide : 460062765 ≤ 460324909) join_0_2 join_0_3

theorem join_1_2 : (twinPrimeSegment 460324909 460849197).card = 1723 := by
  simpa using combineTwinPrimeSegments (by decide : 460324909 ≤ 460587053)
    (by decide : 460587053 ≤ 460849197) join_0_4 join_0_5

theorem join_1_3 : (twinPrimeSegment 460849197 461373485).card = 1728 := by
  simpa using combineTwinPrimeSegments (by decide : 460849197 ≤ 461111341)
    (by decide : 461111341 ≤ 461373485) join_0_6 join_0_7

theorem join_2_0 : (twinPrimeSegment 459276333 460324909).card = 3465 := by
  simpa using combineTwinPrimeSegments (by decide : 459276333 ≤ 459800621)
    (by decide : 459800621 ≤ 460324909) join_1_0 join_1_1

theorem join_2_1 : (twinPrimeSegment 460324909 461373485).card = 3451 := by
  simpa using combineTwinPrimeSegments (by decide : 460324909 ≤ 460849197)
    (by decide : 460849197 ≤ 461373485) join_1_2 join_1_3

theorem join_3_0 : (twinPrimeSegment 459276333 461373485).card = 6916 := by
  simpa using combineTwinPrimeSegments (by decide : 459276333 ≤ 460324909)
    (by decide : 460324909 ≤ 461373485) join_2_0 join_2_1

theorem total : (twinPrimeSegment 459276333 461373485).card = 6916 := join_3_0

end S219All
end Sude.GeneratedTwinScan
