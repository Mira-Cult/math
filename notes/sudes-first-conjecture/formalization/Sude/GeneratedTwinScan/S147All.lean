import Sude.GeneratedTwinScan.S147C00
import Sude.GeneratedTwinScan.S147C01
import Sude.GeneratedTwinScan.S147C02
import Sude.GeneratedTwinScan.S147C03
import Sude.GeneratedTwinScan.S147C04
import Sude.GeneratedTwinScan.S147C05
import Sude.GeneratedTwinScan.S147C06
import Sude.GeneratedTwinScan.S147C07
import Sude.GeneratedTwinScan.S147C08
import Sude.GeneratedTwinScan.S147C09
import Sude.GeneratedTwinScan.S147C10
import Sude.GeneratedTwinScan.S147C11
import Sude.GeneratedTwinScan.S147C12
import Sude.GeneratedTwinScan.S147C13
import Sude.GeneratedTwinScan.S147C14
import Sude.GeneratedTwinScan.S147C15

/-! Combined FT source segment; Lean kernel check required. -/
namespace Sude.GeneratedTwinScan
namespace S147All

theorem join_0_0 : (twinPrimeSegment 308281389 308543533).card = 922 := by
  simpa using combineTwinPrimeSegments (by decide : 308281389 ≤ 308412461)
    (by decide : 308412461 ≤ 308543533) S147C00.total S147C01.total

theorem join_0_1 : (twinPrimeSegment 308543533 308805677).card = 947 := by
  simpa using combineTwinPrimeSegments (by decide : 308543533 ≤ 308674605)
    (by decide : 308674605 ≤ 308805677) S147C02.total S147C03.total

theorem join_0_2 : (twinPrimeSegment 308805677 309067821).card = 923 := by
  simpa using combineTwinPrimeSegments (by decide : 308805677 ≤ 308936749)
    (by decide : 308936749 ≤ 309067821) S147C04.total S147C05.total

theorem join_0_3 : (twinPrimeSegment 309067821 309329965).card = 877 := by
  simpa using combineTwinPrimeSegments (by decide : 309067821 ≤ 309198893)
    (by decide : 309198893 ≤ 309329965) S147C06.total S147C07.total

theorem join_0_4 : (twinPrimeSegment 309329965 309592109).card = 859 := by
  simpa using combineTwinPrimeSegments (by decide : 309329965 ≤ 309461037)
    (by decide : 309461037 ≤ 309592109) S147C08.total S147C09.total

theorem join_0_5 : (twinPrimeSegment 309592109 309854253).card = 869 := by
  simpa using combineTwinPrimeSegments (by decide : 309592109 ≤ 309723181)
    (by decide : 309723181 ≤ 309854253) S147C10.total S147C11.total

theorem join_0_6 : (twinPrimeSegment 309854253 310116397).card = 882 := by
  simpa using combineTwinPrimeSegments (by decide : 309854253 ≤ 309985325)
    (by decide : 309985325 ≤ 310116397) S147C12.total S147C13.total

theorem join_0_7 : (twinPrimeSegment 310116397 310378541).card = 933 := by
  simpa using combineTwinPrimeSegments (by decide : 310116397 ≤ 310247469)
    (by decide : 310247469 ≤ 310378541) S147C14.total S147C15.total

theorem join_1_0 : (twinPrimeSegment 308281389 308805677).card = 1869 := by
  simpa using combineTwinPrimeSegments (by decide : 308281389 ≤ 308543533)
    (by decide : 308543533 ≤ 308805677) join_0_0 join_0_1

theorem join_1_1 : (twinPrimeSegment 308805677 309329965).card = 1800 := by
  simpa using combineTwinPrimeSegments (by decide : 308805677 ≤ 309067821)
    (by decide : 309067821 ≤ 309329965) join_0_2 join_0_3

theorem join_1_2 : (twinPrimeSegment 309329965 309854253).card = 1728 := by
  simpa using combineTwinPrimeSegments (by decide : 309329965 ≤ 309592109)
    (by decide : 309592109 ≤ 309854253) join_0_4 join_0_5

theorem join_1_3 : (twinPrimeSegment 309854253 310378541).card = 1815 := by
  simpa using combineTwinPrimeSegments (by decide : 309854253 ≤ 310116397)
    (by decide : 310116397 ≤ 310378541) join_0_6 join_0_7

theorem join_2_0 : (twinPrimeSegment 308281389 309329965).card = 3669 := by
  simpa using combineTwinPrimeSegments (by decide : 308281389 ≤ 308805677)
    (by decide : 308805677 ≤ 309329965) join_1_0 join_1_1

theorem join_2_1 : (twinPrimeSegment 309329965 310378541).card = 3543 := by
  simpa using combineTwinPrimeSegments (by decide : 309329965 ≤ 309854253)
    (by decide : 309854253 ≤ 310378541) join_1_2 join_1_3

theorem join_3_0 : (twinPrimeSegment 308281389 310378541).card = 7212 := by
  simpa using combineTwinPrimeSegments (by decide : 308281389 ≤ 309329965)
    (by decide : 309329965 ≤ 310378541) join_2_0 join_2_1

theorem total : (twinPrimeSegment 308281389 310378541).card = 7212 := join_3_0

end S147All
end Sude.GeneratedTwinScan
