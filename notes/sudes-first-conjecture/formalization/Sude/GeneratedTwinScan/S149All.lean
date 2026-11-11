import Sude.GeneratedTwinScan.S149C00
import Sude.GeneratedTwinScan.S149C01
import Sude.GeneratedTwinScan.S149C02
import Sude.GeneratedTwinScan.S149C03
import Sude.GeneratedTwinScan.S149C04
import Sude.GeneratedTwinScan.S149C05
import Sude.GeneratedTwinScan.S149C06
import Sude.GeneratedTwinScan.S149C07
import Sude.GeneratedTwinScan.S149C08
import Sude.GeneratedTwinScan.S149C09
import Sude.GeneratedTwinScan.S149C10
import Sude.GeneratedTwinScan.S149C11
import Sude.GeneratedTwinScan.S149C12
import Sude.GeneratedTwinScan.S149C13
import Sude.GeneratedTwinScan.S149C14
import Sude.GeneratedTwinScan.S149C15

/-! Combined FT source segment; Lean kernel check required. -/
namespace Sude.GeneratedTwinScan
namespace S149All

theorem join_0_0 : (twinPrimeSegment 312475693 312737837).card = 873 := by
  simpa using combineTwinPrimeSegments (by decide : 312475693 ≤ 312606765)
    (by decide : 312606765 ≤ 312737837) S149C00.total S149C01.total

theorem join_0_1 : (twinPrimeSegment 312737837 312999981).card = 903 := by
  simpa using combineTwinPrimeSegments (by decide : 312737837 ≤ 312868909)
    (by decide : 312868909 ≤ 312999981) S149C02.total S149C03.total

theorem join_0_2 : (twinPrimeSegment 312999981 313262125).card = 896 := by
  simpa using combineTwinPrimeSegments (by decide : 312999981 ≤ 313131053)
    (by decide : 313131053 ≤ 313262125) S149C04.total S149C05.total

theorem join_0_3 : (twinPrimeSegment 313262125 313524269).card = 876 := by
  simpa using combineTwinPrimeSegments (by decide : 313262125 ≤ 313393197)
    (by decide : 313393197 ≤ 313524269) S149C06.total S149C07.total

theorem join_0_4 : (twinPrimeSegment 313524269 313786413).card = 880 := by
  simpa using combineTwinPrimeSegments (by decide : 313524269 ≤ 313655341)
    (by decide : 313655341 ≤ 313786413) S149C08.total S149C09.total

theorem join_0_5 : (twinPrimeSegment 313786413 314048557).card = 859 := by
  simpa using combineTwinPrimeSegments (by decide : 313786413 ≤ 313917485)
    (by decide : 313917485 ≤ 314048557) S149C10.total S149C11.total

theorem join_0_6 : (twinPrimeSegment 314048557 314310701).card = 919 := by
  simpa using combineTwinPrimeSegments (by decide : 314048557 ≤ 314179629)
    (by decide : 314179629 ≤ 314310701) S149C12.total S149C13.total

theorem join_0_7 : (twinPrimeSegment 314310701 314572845).card = 959 := by
  simpa using combineTwinPrimeSegments (by decide : 314310701 ≤ 314441773)
    (by decide : 314441773 ≤ 314572845) S149C14.total S149C15.total

theorem join_1_0 : (twinPrimeSegment 312475693 312999981).card = 1776 := by
  simpa using combineTwinPrimeSegments (by decide : 312475693 ≤ 312737837)
    (by decide : 312737837 ≤ 312999981) join_0_0 join_0_1

theorem join_1_1 : (twinPrimeSegment 312999981 313524269).card = 1772 := by
  simpa using combineTwinPrimeSegments (by decide : 312999981 ≤ 313262125)
    (by decide : 313262125 ≤ 313524269) join_0_2 join_0_3

theorem join_1_2 : (twinPrimeSegment 313524269 314048557).card = 1739 := by
  simpa using combineTwinPrimeSegments (by decide : 313524269 ≤ 313786413)
    (by decide : 313786413 ≤ 314048557) join_0_4 join_0_5

theorem join_1_3 : (twinPrimeSegment 314048557 314572845).card = 1878 := by
  simpa using combineTwinPrimeSegments (by decide : 314048557 ≤ 314310701)
    (by decide : 314310701 ≤ 314572845) join_0_6 join_0_7

theorem join_2_0 : (twinPrimeSegment 312475693 313524269).card = 3548 := by
  simpa using combineTwinPrimeSegments (by decide : 312475693 ≤ 312999981)
    (by decide : 312999981 ≤ 313524269) join_1_0 join_1_1

theorem join_2_1 : (twinPrimeSegment 313524269 314572845).card = 3617 := by
  simpa using combineTwinPrimeSegments (by decide : 313524269 ≤ 314048557)
    (by decide : 314048557 ≤ 314572845) join_1_2 join_1_3

theorem join_3_0 : (twinPrimeSegment 312475693 314572845).card = 7165 := by
  simpa using combineTwinPrimeSegments (by decide : 312475693 ≤ 313524269)
    (by decide : 313524269 ≤ 314572845) join_2_0 join_2_1

theorem total : (twinPrimeSegment 312475693 314572845).card = 7165 := join_3_0

end S149All
end Sude.GeneratedTwinScan
