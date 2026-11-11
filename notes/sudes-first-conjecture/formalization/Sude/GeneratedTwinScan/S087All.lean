import Sude.GeneratedTwinScan.S087C00
import Sude.GeneratedTwinScan.S087C01
import Sude.GeneratedTwinScan.S087C02
import Sude.GeneratedTwinScan.S087C03
import Sude.GeneratedTwinScan.S087C04
import Sude.GeneratedTwinScan.S087C05
import Sude.GeneratedTwinScan.S087C06
import Sude.GeneratedTwinScan.S087C07
import Sude.GeneratedTwinScan.S087C08
import Sude.GeneratedTwinScan.S087C09
import Sude.GeneratedTwinScan.S087C10
import Sude.GeneratedTwinScan.S087C11
import Sude.GeneratedTwinScan.S087C12
import Sude.GeneratedTwinScan.S087C13
import Sude.GeneratedTwinScan.S087C14
import Sude.GeneratedTwinScan.S087C15

/-! Combined FT source segment; Lean kernel check required. -/
namespace Sude.GeneratedTwinScan
namespace S087All

theorem join_0_0 : (twinPrimeSegment 182452269 182714413).card = 906 := by
  simpa using combineTwinPrimeSegments (by decide : 182452269 ≤ 182583341)
    (by decide : 182583341 ≤ 182714413) S087C00.total S087C01.total

theorem join_0_1 : (twinPrimeSegment 182714413 182976557).card = 926 := by
  simpa using combineTwinPrimeSegments (by decide : 182714413 ≤ 182845485)
    (by decide : 182845485 ≤ 182976557) S087C02.total S087C03.total

theorem join_0_2 : (twinPrimeSegment 182976557 183238701).card = 964 := by
  simpa using combineTwinPrimeSegments (by decide : 182976557 ≤ 183107629)
    (by decide : 183107629 ≤ 183238701) S087C04.total S087C05.total

theorem join_0_3 : (twinPrimeSegment 183238701 183500845).card = 972 := by
  simpa using combineTwinPrimeSegments (by decide : 183238701 ≤ 183369773)
    (by decide : 183369773 ≤ 183500845) S087C06.total S087C07.total

theorem join_0_4 : (twinPrimeSegment 183500845 183762989).card = 965 := by
  simpa using combineTwinPrimeSegments (by decide : 183500845 ≤ 183631917)
    (by decide : 183631917 ≤ 183762989) S087C08.total S087C09.total

theorem join_0_5 : (twinPrimeSegment 183762989 184025133).card = 934 := by
  simpa using combineTwinPrimeSegments (by decide : 183762989 ≤ 183894061)
    (by decide : 183894061 ≤ 184025133) S087C10.total S087C11.total

theorem join_0_6 : (twinPrimeSegment 184025133 184287277).card = 963 := by
  simpa using combineTwinPrimeSegments (by decide : 184025133 ≤ 184156205)
    (by decide : 184156205 ≤ 184287277) S087C12.total S087C13.total

theorem join_0_7 : (twinPrimeSegment 184287277 184549421).card = 970 := by
  simpa using combineTwinPrimeSegments (by decide : 184287277 ≤ 184418349)
    (by decide : 184418349 ≤ 184549421) S087C14.total S087C15.total

theorem join_1_0 : (twinPrimeSegment 182452269 182976557).card = 1832 := by
  simpa using combineTwinPrimeSegments (by decide : 182452269 ≤ 182714413)
    (by decide : 182714413 ≤ 182976557) join_0_0 join_0_1

theorem join_1_1 : (twinPrimeSegment 182976557 183500845).card = 1936 := by
  simpa using combineTwinPrimeSegments (by decide : 182976557 ≤ 183238701)
    (by decide : 183238701 ≤ 183500845) join_0_2 join_0_3

theorem join_1_2 : (twinPrimeSegment 183500845 184025133).card = 1899 := by
  simpa using combineTwinPrimeSegments (by decide : 183500845 ≤ 183762989)
    (by decide : 183762989 ≤ 184025133) join_0_4 join_0_5

theorem join_1_3 : (twinPrimeSegment 184025133 184549421).card = 1933 := by
  simpa using combineTwinPrimeSegments (by decide : 184025133 ≤ 184287277)
    (by decide : 184287277 ≤ 184549421) join_0_6 join_0_7

theorem join_2_0 : (twinPrimeSegment 182452269 183500845).card = 3768 := by
  simpa using combineTwinPrimeSegments (by decide : 182452269 ≤ 182976557)
    (by decide : 182976557 ≤ 183500845) join_1_0 join_1_1

theorem join_2_1 : (twinPrimeSegment 183500845 184549421).card = 3832 := by
  simpa using combineTwinPrimeSegments (by decide : 183500845 ≤ 184025133)
    (by decide : 184025133 ≤ 184549421) join_1_2 join_1_3

theorem join_3_0 : (twinPrimeSegment 182452269 184549421).card = 7600 := by
  simpa using combineTwinPrimeSegments (by decide : 182452269 ≤ 183500845)
    (by decide : 183500845 ≤ 184549421) join_2_0 join_2_1

theorem total : (twinPrimeSegment 182452269 184549421).card = 7600 := join_3_0

end S087All
end Sude.GeneratedTwinScan
