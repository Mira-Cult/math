import Sude.GeneratedTwinScan.S049C00
import Sude.GeneratedTwinScan.S049C01
import Sude.GeneratedTwinScan.S049C02
import Sude.GeneratedTwinScan.S049C03
import Sude.GeneratedTwinScan.S049C04
import Sude.GeneratedTwinScan.S049C05
import Sude.GeneratedTwinScan.S049C06
import Sude.GeneratedTwinScan.S049C07
import Sude.GeneratedTwinScan.S049C08
import Sude.GeneratedTwinScan.S049C09
import Sude.GeneratedTwinScan.S049C10
import Sude.GeneratedTwinScan.S049C11
import Sude.GeneratedTwinScan.S049C12
import Sude.GeneratedTwinScan.S049C13
import Sude.GeneratedTwinScan.S049C14
import Sude.GeneratedTwinScan.S049C15

/-! Combined FT source segment; Lean kernel check required. -/
namespace Sude.GeneratedTwinScan
namespace S049All

theorem join_0_0 : (twinPrimeSegment 102760493 103022637).card = 1047 := by
  simpa using combineTwinPrimeSegments (by decide : 102760493 ≤ 102891565)
    (by decide : 102891565 ≤ 103022637) S049C00.total S049C01.total

theorem join_0_1 : (twinPrimeSegment 103022637 103284781).card = 976 := by
  simpa using combineTwinPrimeSegments (by decide : 103022637 ≤ 103153709)
    (by decide : 103153709 ≤ 103284781) S049C02.total S049C03.total

theorem join_0_2 : (twinPrimeSegment 103284781 103546925).card = 1057 := by
  simpa using combineTwinPrimeSegments (by decide : 103284781 ≤ 103415853)
    (by decide : 103415853 ≤ 103546925) S049C04.total S049C05.total

theorem join_0_3 : (twinPrimeSegment 103546925 103809069).card = 1036 := by
  simpa using combineTwinPrimeSegments (by decide : 103546925 ≤ 103677997)
    (by decide : 103677997 ≤ 103809069) S049C06.total S049C07.total

theorem join_0_4 : (twinPrimeSegment 103809069 104071213).card = 1039 := by
  simpa using combineTwinPrimeSegments (by decide : 103809069 ≤ 103940141)
    (by decide : 103940141 ≤ 104071213) S049C08.total S049C09.total

theorem join_0_5 : (twinPrimeSegment 104071213 104333357).card = 1046 := by
  simpa using combineTwinPrimeSegments (by decide : 104071213 ≤ 104202285)
    (by decide : 104202285 ≤ 104333357) S049C10.total S049C11.total

theorem join_0_6 : (twinPrimeSegment 104333357 104595501).card = 1023 := by
  simpa using combineTwinPrimeSegments (by decide : 104333357 ≤ 104464429)
    (by decide : 104464429 ≤ 104595501) S049C12.total S049C13.total

theorem join_0_7 : (twinPrimeSegment 104595501 104857645).card = 1000 := by
  simpa using combineTwinPrimeSegments (by decide : 104595501 ≤ 104726573)
    (by decide : 104726573 ≤ 104857645) S049C14.total S049C15.total

theorem join_1_0 : (twinPrimeSegment 102760493 103284781).card = 2023 := by
  simpa using combineTwinPrimeSegments (by decide : 102760493 ≤ 103022637)
    (by decide : 103022637 ≤ 103284781) join_0_0 join_0_1

theorem join_1_1 : (twinPrimeSegment 103284781 103809069).card = 2093 := by
  simpa using combineTwinPrimeSegments (by decide : 103284781 ≤ 103546925)
    (by decide : 103546925 ≤ 103809069) join_0_2 join_0_3

theorem join_1_2 : (twinPrimeSegment 103809069 104333357).card = 2085 := by
  simpa using combineTwinPrimeSegments (by decide : 103809069 ≤ 104071213)
    (by decide : 104071213 ≤ 104333357) join_0_4 join_0_5

theorem join_1_3 : (twinPrimeSegment 104333357 104857645).card = 2023 := by
  simpa using combineTwinPrimeSegments (by decide : 104333357 ≤ 104595501)
    (by decide : 104595501 ≤ 104857645) join_0_6 join_0_7

theorem join_2_0 : (twinPrimeSegment 102760493 103809069).card = 4116 := by
  simpa using combineTwinPrimeSegments (by decide : 102760493 ≤ 103284781)
    (by decide : 103284781 ≤ 103809069) join_1_0 join_1_1

theorem join_2_1 : (twinPrimeSegment 103809069 104857645).card = 4108 := by
  simpa using combineTwinPrimeSegments (by decide : 103809069 ≤ 104333357)
    (by decide : 104333357 ≤ 104857645) join_1_2 join_1_3

theorem join_3_0 : (twinPrimeSegment 102760493 104857645).card = 8224 := by
  simpa using combineTwinPrimeSegments (by decide : 102760493 ≤ 103809069)
    (by decide : 103809069 ≤ 104857645) join_2_0 join_2_1

theorem total : (twinPrimeSegment 102760493 104857645).card = 8224 := join_3_0

end S049All
end Sude.GeneratedTwinScan
