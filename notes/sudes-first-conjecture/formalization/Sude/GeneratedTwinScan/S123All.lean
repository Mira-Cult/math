import Sude.GeneratedTwinScan.S123C00
import Sude.GeneratedTwinScan.S123C01
import Sude.GeneratedTwinScan.S123C02
import Sude.GeneratedTwinScan.S123C03
import Sude.GeneratedTwinScan.S123C04
import Sude.GeneratedTwinScan.S123C05
import Sude.GeneratedTwinScan.S123C06
import Sude.GeneratedTwinScan.S123C07
import Sude.GeneratedTwinScan.S123C08
import Sude.GeneratedTwinScan.S123C09
import Sude.GeneratedTwinScan.S123C10
import Sude.GeneratedTwinScan.S123C11
import Sude.GeneratedTwinScan.S123C12
import Sude.GeneratedTwinScan.S123C13
import Sude.GeneratedTwinScan.S123C14
import Sude.GeneratedTwinScan.S123C15

/-! Combined FT source segment; Lean kernel check required. -/
namespace Sude.GeneratedTwinScan
namespace S123All

theorem join_0_0 : (twinPrimeSegment 257949741 258211885).card = 913 := by
  simpa using combineTwinPrimeSegments (by decide : 257949741 ≤ 258080813)
    (by decide : 258080813 ≤ 258211885) S123C00.total S123C01.total

theorem join_0_1 : (twinPrimeSegment 258211885 258474029).card = 910 := by
  simpa using combineTwinPrimeSegments (by decide : 258211885 ≤ 258342957)
    (by decide : 258342957 ≤ 258474029) S123C02.total S123C03.total

theorem join_0_2 : (twinPrimeSegment 258474029 258736173).card = 894 := by
  simpa using combineTwinPrimeSegments (by decide : 258474029 ≤ 258605101)
    (by decide : 258605101 ≤ 258736173) S123C04.total S123C05.total

theorem join_0_3 : (twinPrimeSegment 258736173 258998317).card = 934 := by
  simpa using combineTwinPrimeSegments (by decide : 258736173 ≤ 258867245)
    (by decide : 258867245 ≤ 258998317) S123C06.total S123C07.total

theorem join_0_4 : (twinPrimeSegment 258998317 259260461).card = 932 := by
  simpa using combineTwinPrimeSegments (by decide : 258998317 ≤ 259129389)
    (by decide : 259129389 ≤ 259260461) S123C08.total S123C09.total

theorem join_0_5 : (twinPrimeSegment 259260461 259522605).card = 925 := by
  simpa using combineTwinPrimeSegments (by decide : 259260461 ≤ 259391533)
    (by decide : 259391533 ≤ 259522605) S123C10.total S123C11.total

theorem join_0_6 : (twinPrimeSegment 259522605 259784749).card = 905 := by
  simpa using combineTwinPrimeSegments (by decide : 259522605 ≤ 259653677)
    (by decide : 259653677 ≤ 259784749) S123C12.total S123C13.total

theorem join_0_7 : (twinPrimeSegment 259784749 260046893).card = 916 := by
  simpa using combineTwinPrimeSegments (by decide : 259784749 ≤ 259915821)
    (by decide : 259915821 ≤ 260046893) S123C14.total S123C15.total

theorem join_1_0 : (twinPrimeSegment 257949741 258474029).card = 1823 := by
  simpa using combineTwinPrimeSegments (by decide : 257949741 ≤ 258211885)
    (by decide : 258211885 ≤ 258474029) join_0_0 join_0_1

theorem join_1_1 : (twinPrimeSegment 258474029 258998317).card = 1828 := by
  simpa using combineTwinPrimeSegments (by decide : 258474029 ≤ 258736173)
    (by decide : 258736173 ≤ 258998317) join_0_2 join_0_3

theorem join_1_2 : (twinPrimeSegment 258998317 259522605).card = 1857 := by
  simpa using combineTwinPrimeSegments (by decide : 258998317 ≤ 259260461)
    (by decide : 259260461 ≤ 259522605) join_0_4 join_0_5

theorem join_1_3 : (twinPrimeSegment 259522605 260046893).card = 1821 := by
  simpa using combineTwinPrimeSegments (by decide : 259522605 ≤ 259784749)
    (by decide : 259784749 ≤ 260046893) join_0_6 join_0_7

theorem join_2_0 : (twinPrimeSegment 257949741 258998317).card = 3651 := by
  simpa using combineTwinPrimeSegments (by decide : 257949741 ≤ 258474029)
    (by decide : 258474029 ≤ 258998317) join_1_0 join_1_1

theorem join_2_1 : (twinPrimeSegment 258998317 260046893).card = 3678 := by
  simpa using combineTwinPrimeSegments (by decide : 258998317 ≤ 259522605)
    (by decide : 259522605 ≤ 260046893) join_1_2 join_1_3

theorem join_3_0 : (twinPrimeSegment 257949741 260046893).card = 7329 := by
  simpa using combineTwinPrimeSegments (by decide : 257949741 ≤ 258998317)
    (by decide : 258998317 ≤ 260046893) join_2_0 join_2_1

theorem total : (twinPrimeSegment 257949741 260046893).card = 7329 := join_3_0

end S123All
end Sude.GeneratedTwinScan
