import Sude.GeneratedTwinScan.S071C00
import Sude.GeneratedTwinScan.S071C01
import Sude.GeneratedTwinScan.S071C02
import Sude.GeneratedTwinScan.S071C03
import Sude.GeneratedTwinScan.S071C04
import Sude.GeneratedTwinScan.S071C05
import Sude.GeneratedTwinScan.S071C06
import Sude.GeneratedTwinScan.S071C07
import Sude.GeneratedTwinScan.S071C08
import Sude.GeneratedTwinScan.S071C09
import Sude.GeneratedTwinScan.S071C10
import Sude.GeneratedTwinScan.S071C11
import Sude.GeneratedTwinScan.S071C12
import Sude.GeneratedTwinScan.S071C13
import Sude.GeneratedTwinScan.S071C14
import Sude.GeneratedTwinScan.S071C15

/-! Combined FT source segment; Lean kernel check required. -/
namespace Sude.GeneratedTwinScan
namespace S071All

theorem join_0_0 : (twinPrimeSegment 148897837 149159981).card = 997 := by
  simpa using combineTwinPrimeSegments (by decide : 148897837 ≤ 149028909)
    (by decide : 149028909 ≤ 149159981) S071C00.total S071C01.total

theorem join_0_1 : (twinPrimeSegment 149159981 149422125).card = 985 := by
  simpa using combineTwinPrimeSegments (by decide : 149159981 ≤ 149291053)
    (by decide : 149291053 ≤ 149422125) S071C02.total S071C03.total

theorem join_0_2 : (twinPrimeSegment 149422125 149684269).card = 921 := by
  simpa using combineTwinPrimeSegments (by decide : 149422125 ≤ 149553197)
    (by decide : 149553197 ≤ 149684269) S071C04.total S071C05.total

theorem join_0_3 : (twinPrimeSegment 149684269 149946413).card = 942 := by
  simpa using combineTwinPrimeSegments (by decide : 149684269 ≤ 149815341)
    (by decide : 149815341 ≤ 149946413) S071C06.total S071C07.total

theorem join_0_4 : (twinPrimeSegment 149946413 150208557).card = 985 := by
  simpa using combineTwinPrimeSegments (by decide : 149946413 ≤ 150077485)
    (by decide : 150077485 ≤ 150208557) S071C08.total S071C09.total

theorem join_0_5 : (twinPrimeSegment 150208557 150470701).card = 974 := by
  simpa using combineTwinPrimeSegments (by decide : 150208557 ≤ 150339629)
    (by decide : 150339629 ≤ 150470701) S071C10.total S071C11.total

theorem join_0_6 : (twinPrimeSegment 150470701 150732845).card = 966 := by
  simpa using combineTwinPrimeSegments (by decide : 150470701 ≤ 150601773)
    (by decide : 150601773 ≤ 150732845) S071C12.total S071C13.total

theorem join_0_7 : (twinPrimeSegment 150732845 150994989).card = 953 := by
  simpa using combineTwinPrimeSegments (by decide : 150732845 ≤ 150863917)
    (by decide : 150863917 ≤ 150994989) S071C14.total S071C15.total

theorem join_1_0 : (twinPrimeSegment 148897837 149422125).card = 1982 := by
  simpa using combineTwinPrimeSegments (by decide : 148897837 ≤ 149159981)
    (by decide : 149159981 ≤ 149422125) join_0_0 join_0_1

theorem join_1_1 : (twinPrimeSegment 149422125 149946413).card = 1863 := by
  simpa using combineTwinPrimeSegments (by decide : 149422125 ≤ 149684269)
    (by decide : 149684269 ≤ 149946413) join_0_2 join_0_3

theorem join_1_2 : (twinPrimeSegment 149946413 150470701).card = 1959 := by
  simpa using combineTwinPrimeSegments (by decide : 149946413 ≤ 150208557)
    (by decide : 150208557 ≤ 150470701) join_0_4 join_0_5

theorem join_1_3 : (twinPrimeSegment 150470701 150994989).card = 1919 := by
  simpa using combineTwinPrimeSegments (by decide : 150470701 ≤ 150732845)
    (by decide : 150732845 ≤ 150994989) join_0_6 join_0_7

theorem join_2_0 : (twinPrimeSegment 148897837 149946413).card = 3845 := by
  simpa using combineTwinPrimeSegments (by decide : 148897837 ≤ 149422125)
    (by decide : 149422125 ≤ 149946413) join_1_0 join_1_1

theorem join_2_1 : (twinPrimeSegment 149946413 150994989).card = 3878 := by
  simpa using combineTwinPrimeSegments (by decide : 149946413 ≤ 150470701)
    (by decide : 150470701 ≤ 150994989) join_1_2 join_1_3

theorem join_3_0 : (twinPrimeSegment 148897837 150994989).card = 7723 := by
  simpa using combineTwinPrimeSegments (by decide : 148897837 ≤ 149946413)
    (by decide : 149946413 ≤ 150994989) join_2_0 join_2_1

theorem total : (twinPrimeSegment 148897837 150994989).card = 7723 := join_3_0

end S071All
end Sude.GeneratedTwinScan
