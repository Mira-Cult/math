import Sude.GeneratedTwinScan.S227C00
import Sude.GeneratedTwinScan.S227C01
import Sude.GeneratedTwinScan.S227C02
import Sude.GeneratedTwinScan.S227C03
import Sude.GeneratedTwinScan.S227C04
import Sude.GeneratedTwinScan.S227C05
import Sude.GeneratedTwinScan.S227C06
import Sude.GeneratedTwinScan.S227C07
import Sude.GeneratedTwinScan.S227C08
import Sude.GeneratedTwinScan.S227C09
import Sude.GeneratedTwinScan.S227C10
import Sude.GeneratedTwinScan.S227C11
import Sude.GeneratedTwinScan.S227C12
import Sude.GeneratedTwinScan.S227C13
import Sude.GeneratedTwinScan.S227C14
import Sude.GeneratedTwinScan.S227C15

/-! Combined FT source segment; Lean kernel check required. -/
namespace Sude.GeneratedTwinScan
namespace S227All

theorem join_0_0 : (twinPrimeSegment 476053549 476315693).card = 893 := by
  simpa using combineTwinPrimeSegments (by decide : 476053549 ≤ 476184621)
    (by decide : 476184621 ≤ 476315693) S227C00.total S227C01.total

theorem join_0_1 : (twinPrimeSegment 476315693 476577837).card = 861 := by
  simpa using combineTwinPrimeSegments (by decide : 476315693 ≤ 476446765)
    (by decide : 476446765 ≤ 476577837) S227C02.total S227C03.total

theorem join_0_2 : (twinPrimeSegment 476577837 476839981).card = 859 := by
  simpa using combineTwinPrimeSegments (by decide : 476577837 ≤ 476708909)
    (by decide : 476708909 ≤ 476839981) S227C04.total S227C05.total

theorem join_0_3 : (twinPrimeSegment 476839981 477102125).card = 862 := by
  simpa using combineTwinPrimeSegments (by decide : 476839981 ≤ 476971053)
    (by decide : 476971053 ≤ 477102125) S227C06.total S227C07.total

theorem join_0_4 : (twinPrimeSegment 477102125 477364269).card = 842 := by
  simpa using combineTwinPrimeSegments (by decide : 477102125 ≤ 477233197)
    (by decide : 477233197 ≤ 477364269) S227C08.total S227C09.total

theorem join_0_5 : (twinPrimeSegment 477364269 477626413).card = 915 := by
  simpa using combineTwinPrimeSegments (by decide : 477364269 ≤ 477495341)
    (by decide : 477495341 ≤ 477626413) S227C10.total S227C11.total

theorem join_0_6 : (twinPrimeSegment 477626413 477888557).card = 871 := by
  simpa using combineTwinPrimeSegments (by decide : 477626413 ≤ 477757485)
    (by decide : 477757485 ≤ 477888557) S227C12.total S227C13.total

theorem join_0_7 : (twinPrimeSegment 477888557 478150701).card = 880 := by
  simpa using combineTwinPrimeSegments (by decide : 477888557 ≤ 478019629)
    (by decide : 478019629 ≤ 478150701) S227C14.total S227C15.total

theorem join_1_0 : (twinPrimeSegment 476053549 476577837).card = 1754 := by
  simpa using combineTwinPrimeSegments (by decide : 476053549 ≤ 476315693)
    (by decide : 476315693 ≤ 476577837) join_0_0 join_0_1

theorem join_1_1 : (twinPrimeSegment 476577837 477102125).card = 1721 := by
  simpa using combineTwinPrimeSegments (by decide : 476577837 ≤ 476839981)
    (by decide : 476839981 ≤ 477102125) join_0_2 join_0_3

theorem join_1_2 : (twinPrimeSegment 477102125 477626413).card = 1757 := by
  simpa using combineTwinPrimeSegments (by decide : 477102125 ≤ 477364269)
    (by decide : 477364269 ≤ 477626413) join_0_4 join_0_5

theorem join_1_3 : (twinPrimeSegment 477626413 478150701).card = 1751 := by
  simpa using combineTwinPrimeSegments (by decide : 477626413 ≤ 477888557)
    (by decide : 477888557 ≤ 478150701) join_0_6 join_0_7

theorem join_2_0 : (twinPrimeSegment 476053549 477102125).card = 3475 := by
  simpa using combineTwinPrimeSegments (by decide : 476053549 ≤ 476577837)
    (by decide : 476577837 ≤ 477102125) join_1_0 join_1_1

theorem join_2_1 : (twinPrimeSegment 477102125 478150701).card = 3508 := by
  simpa using combineTwinPrimeSegments (by decide : 477102125 ≤ 477626413)
    (by decide : 477626413 ≤ 478150701) join_1_2 join_1_3

theorem join_3_0 : (twinPrimeSegment 476053549 478150701).card = 6983 := by
  simpa using combineTwinPrimeSegments (by decide : 476053549 ≤ 477102125)
    (by decide : 477102125 ≤ 478150701) join_2_0 join_2_1

theorem total : (twinPrimeSegment 476053549 478150701).card = 6983 := join_3_0

end S227All
end Sude.GeneratedTwinScan
