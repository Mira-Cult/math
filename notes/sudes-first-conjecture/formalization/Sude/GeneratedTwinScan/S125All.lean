import Sude.GeneratedTwinScan.S125C00
import Sude.GeneratedTwinScan.S125C01
import Sude.GeneratedTwinScan.S125C02
import Sude.GeneratedTwinScan.S125C03
import Sude.GeneratedTwinScan.S125C04
import Sude.GeneratedTwinScan.S125C05
import Sude.GeneratedTwinScan.S125C06
import Sude.GeneratedTwinScan.S125C07
import Sude.GeneratedTwinScan.S125C08
import Sude.GeneratedTwinScan.S125C09
import Sude.GeneratedTwinScan.S125C10
import Sude.GeneratedTwinScan.S125C11
import Sude.GeneratedTwinScan.S125C12
import Sude.GeneratedTwinScan.S125C13
import Sude.GeneratedTwinScan.S125C14
import Sude.GeneratedTwinScan.S125C15

/-! Combined FT source segment; Lean kernel check required. -/
namespace Sude.GeneratedTwinScan
namespace S125All

theorem join_0_0 : (twinPrimeSegment 262144045 262406189).card = 924 := by
  simpa using combineTwinPrimeSegments (by decide : 262144045 ≤ 262275117)
    (by decide : 262275117 ≤ 262406189) S125C00.total S125C01.total

theorem join_0_1 : (twinPrimeSegment 262406189 262668333).card = 911 := by
  simpa using combineTwinPrimeSegments (by decide : 262406189 ≤ 262537261)
    (by decide : 262537261 ≤ 262668333) S125C02.total S125C03.total

theorem join_0_2 : (twinPrimeSegment 262668333 262930477).card = 888 := by
  simpa using combineTwinPrimeSegments (by decide : 262668333 ≤ 262799405)
    (by decide : 262799405 ≤ 262930477) S125C04.total S125C05.total

theorem join_0_3 : (twinPrimeSegment 262930477 263192621).card = 885 := by
  simpa using combineTwinPrimeSegments (by decide : 262930477 ≤ 263061549)
    (by decide : 263061549 ≤ 263192621) S125C06.total S125C07.total

theorem join_0_4 : (twinPrimeSegment 263192621 263454765).card = 964 := by
  simpa using combineTwinPrimeSegments (by decide : 263192621 ≤ 263323693)
    (by decide : 263323693 ≤ 263454765) S125C08.total S125C09.total

theorem join_0_5 : (twinPrimeSegment 263454765 263716909).card = 925 := by
  simpa using combineTwinPrimeSegments (by decide : 263454765 ≤ 263585837)
    (by decide : 263585837 ≤ 263716909) S125C10.total S125C11.total

theorem join_0_6 : (twinPrimeSegment 263716909 263979053).card = 899 := by
  simpa using combineTwinPrimeSegments (by decide : 263716909 ≤ 263847981)
    (by decide : 263847981 ≤ 263979053) S125C12.total S125C13.total

theorem join_0_7 : (twinPrimeSegment 263979053 264241197).card = 924 := by
  simpa using combineTwinPrimeSegments (by decide : 263979053 ≤ 264110125)
    (by decide : 264110125 ≤ 264241197) S125C14.total S125C15.total

theorem join_1_0 : (twinPrimeSegment 262144045 262668333).card = 1835 := by
  simpa using combineTwinPrimeSegments (by decide : 262144045 ≤ 262406189)
    (by decide : 262406189 ≤ 262668333) join_0_0 join_0_1

theorem join_1_1 : (twinPrimeSegment 262668333 263192621).card = 1773 := by
  simpa using combineTwinPrimeSegments (by decide : 262668333 ≤ 262930477)
    (by decide : 262930477 ≤ 263192621) join_0_2 join_0_3

theorem join_1_2 : (twinPrimeSegment 263192621 263716909).card = 1889 := by
  simpa using combineTwinPrimeSegments (by decide : 263192621 ≤ 263454765)
    (by decide : 263454765 ≤ 263716909) join_0_4 join_0_5

theorem join_1_3 : (twinPrimeSegment 263716909 264241197).card = 1823 := by
  simpa using combineTwinPrimeSegments (by decide : 263716909 ≤ 263979053)
    (by decide : 263979053 ≤ 264241197) join_0_6 join_0_7

theorem join_2_0 : (twinPrimeSegment 262144045 263192621).card = 3608 := by
  simpa using combineTwinPrimeSegments (by decide : 262144045 ≤ 262668333)
    (by decide : 262668333 ≤ 263192621) join_1_0 join_1_1

theorem join_2_1 : (twinPrimeSegment 263192621 264241197).card = 3712 := by
  simpa using combineTwinPrimeSegments (by decide : 263192621 ≤ 263716909)
    (by decide : 263716909 ≤ 264241197) join_1_2 join_1_3

theorem join_3_0 : (twinPrimeSegment 262144045 264241197).card = 7320 := by
  simpa using combineTwinPrimeSegments (by decide : 262144045 ≤ 263192621)
    (by decide : 263192621 ≤ 264241197) join_2_0 join_2_1

theorem total : (twinPrimeSegment 262144045 264241197).card = 7320 := join_3_0

end S125All
end Sude.GeneratedTwinScan
