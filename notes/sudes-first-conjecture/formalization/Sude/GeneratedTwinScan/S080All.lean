import Sude.GeneratedTwinScan.S080C00
import Sude.GeneratedTwinScan.S080C01
import Sude.GeneratedTwinScan.S080C02
import Sude.GeneratedTwinScan.S080C03
import Sude.GeneratedTwinScan.S080C04
import Sude.GeneratedTwinScan.S080C05
import Sude.GeneratedTwinScan.S080C06
import Sude.GeneratedTwinScan.S080C07
import Sude.GeneratedTwinScan.S080C08
import Sude.GeneratedTwinScan.S080C09
import Sude.GeneratedTwinScan.S080C10
import Sude.GeneratedTwinScan.S080C11
import Sude.GeneratedTwinScan.S080C12
import Sude.GeneratedTwinScan.S080C13
import Sude.GeneratedTwinScan.S080C14
import Sude.GeneratedTwinScan.S080C15

/-! Combined FT source segment; Lean kernel check required. -/
namespace Sude.GeneratedTwinScan
namespace S080All

theorem join_0_0 : (twinPrimeSegment 167772205 168034349).card = 960 := by
  simpa using combineTwinPrimeSegments (by decide : 167772205 ≤ 167903277)
    (by decide : 167903277 ≤ 168034349) S080C00.total S080C01.total

theorem join_0_1 : (twinPrimeSegment 168034349 168296493).card = 957 := by
  simpa using combineTwinPrimeSegments (by decide : 168034349 ≤ 168165421)
    (by decide : 168165421 ≤ 168296493) S080C02.total S080C03.total

theorem join_0_2 : (twinPrimeSegment 168296493 168558637).card = 972 := by
  simpa using combineTwinPrimeSegments (by decide : 168296493 ≤ 168427565)
    (by decide : 168427565 ≤ 168558637) S080C04.total S080C05.total

theorem join_0_3 : (twinPrimeSegment 168558637 168820781).card = 966 := by
  simpa using combineTwinPrimeSegments (by decide : 168558637 ≤ 168689709)
    (by decide : 168689709 ≤ 168820781) S080C06.total S080C07.total

theorem join_0_4 : (twinPrimeSegment 168820781 169082925).card = 955 := by
  simpa using combineTwinPrimeSegments (by decide : 168820781 ≤ 168951853)
    (by decide : 168951853 ≤ 169082925) S080C08.total S080C09.total

theorem join_0_5 : (twinPrimeSegment 169082925 169345069).card = 986 := by
  simpa using combineTwinPrimeSegments (by decide : 169082925 ≤ 169213997)
    (by decide : 169213997 ≤ 169345069) S080C10.total S080C11.total

theorem join_0_6 : (twinPrimeSegment 169345069 169607213).card = 955 := by
  simpa using combineTwinPrimeSegments (by decide : 169345069 ≤ 169476141)
    (by decide : 169476141 ≤ 169607213) S080C12.total S080C13.total

theorem join_0_7 : (twinPrimeSegment 169607213 169869357).card = 938 := by
  simpa using combineTwinPrimeSegments (by decide : 169607213 ≤ 169738285)
    (by decide : 169738285 ≤ 169869357) S080C14.total S080C15.total

theorem join_1_0 : (twinPrimeSegment 167772205 168296493).card = 1917 := by
  simpa using combineTwinPrimeSegments (by decide : 167772205 ≤ 168034349)
    (by decide : 168034349 ≤ 168296493) join_0_0 join_0_1

theorem join_1_1 : (twinPrimeSegment 168296493 168820781).card = 1938 := by
  simpa using combineTwinPrimeSegments (by decide : 168296493 ≤ 168558637)
    (by decide : 168558637 ≤ 168820781) join_0_2 join_0_3

theorem join_1_2 : (twinPrimeSegment 168820781 169345069).card = 1941 := by
  simpa using combineTwinPrimeSegments (by decide : 168820781 ≤ 169082925)
    (by decide : 169082925 ≤ 169345069) join_0_4 join_0_5

theorem join_1_3 : (twinPrimeSegment 169345069 169869357).card = 1893 := by
  simpa using combineTwinPrimeSegments (by decide : 169345069 ≤ 169607213)
    (by decide : 169607213 ≤ 169869357) join_0_6 join_0_7

theorem join_2_0 : (twinPrimeSegment 167772205 168820781).card = 3855 := by
  simpa using combineTwinPrimeSegments (by decide : 167772205 ≤ 168296493)
    (by decide : 168296493 ≤ 168820781) join_1_0 join_1_1

theorem join_2_1 : (twinPrimeSegment 168820781 169869357).card = 3834 := by
  simpa using combineTwinPrimeSegments (by decide : 168820781 ≤ 169345069)
    (by decide : 169345069 ≤ 169869357) join_1_2 join_1_3

theorem join_3_0 : (twinPrimeSegment 167772205 169869357).card = 7689 := by
  simpa using combineTwinPrimeSegments (by decide : 167772205 ≤ 168820781)
    (by decide : 168820781 ≤ 169869357) join_2_0 join_2_1

theorem total : (twinPrimeSegment 167772205 169869357).card = 7689 := join_3_0

end S080All
end Sude.GeneratedTwinScan
