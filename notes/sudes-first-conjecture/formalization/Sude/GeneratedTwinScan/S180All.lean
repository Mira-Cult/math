import Sude.GeneratedTwinScan.S180C00
import Sude.GeneratedTwinScan.S180C01
import Sude.GeneratedTwinScan.S180C02
import Sude.GeneratedTwinScan.S180C03
import Sude.GeneratedTwinScan.S180C04
import Sude.GeneratedTwinScan.S180C05
import Sude.GeneratedTwinScan.S180C06
import Sude.GeneratedTwinScan.S180C07
import Sude.GeneratedTwinScan.S180C08
import Sude.GeneratedTwinScan.S180C09
import Sude.GeneratedTwinScan.S180C10
import Sude.GeneratedTwinScan.S180C11
import Sude.GeneratedTwinScan.S180C12
import Sude.GeneratedTwinScan.S180C13
import Sude.GeneratedTwinScan.S180C14
import Sude.GeneratedTwinScan.S180C15

/-! Combined FT source segment; Lean kernel check required. -/
namespace Sude.GeneratedTwinScan
namespace S180All

theorem join_0_0 : (twinPrimeSegment 377487405 377749549).card = 858 := by
  simpa using combineTwinPrimeSegments (by decide : 377487405 ≤ 377618477)
    (by decide : 377618477 ≤ 377749549) S180C00.total S180C01.total

theorem join_0_1 : (twinPrimeSegment 377749549 378011693).card = 912 := by
  simpa using combineTwinPrimeSegments (by decide : 377749549 ≤ 377880621)
    (by decide : 377880621 ≤ 378011693) S180C02.total S180C03.total

theorem join_0_2 : (twinPrimeSegment 378011693 378273837).card = 893 := by
  simpa using combineTwinPrimeSegments (by decide : 378011693 ≤ 378142765)
    (by decide : 378142765 ≤ 378273837) S180C04.total S180C05.total

theorem join_0_3 : (twinPrimeSegment 378273837 378535981).card = 898 := by
  simpa using combineTwinPrimeSegments (by decide : 378273837 ≤ 378404909)
    (by decide : 378404909 ≤ 378535981) S180C06.total S180C07.total

theorem join_0_4 : (twinPrimeSegment 378535981 378798125).card = 861 := by
  simpa using combineTwinPrimeSegments (by decide : 378535981 ≤ 378667053)
    (by decide : 378667053 ≤ 378798125) S180C08.total S180C09.total

theorem join_0_5 : (twinPrimeSegment 378798125 379060269).card = 875 := by
  simpa using combineTwinPrimeSegments (by decide : 378798125 ≤ 378929197)
    (by decide : 378929197 ≤ 379060269) S180C10.total S180C11.total

theorem join_0_6 : (twinPrimeSegment 379060269 379322413).card = 887 := by
  simpa using combineTwinPrimeSegments (by decide : 379060269 ≤ 379191341)
    (by decide : 379191341 ≤ 379322413) S180C12.total S180C13.total

theorem join_0_7 : (twinPrimeSegment 379322413 379584557).card = 860 := by
  simpa using combineTwinPrimeSegments (by decide : 379322413 ≤ 379453485)
    (by decide : 379453485 ≤ 379584557) S180C14.total S180C15.total

theorem join_1_0 : (twinPrimeSegment 377487405 378011693).card = 1770 := by
  simpa using combineTwinPrimeSegments (by decide : 377487405 ≤ 377749549)
    (by decide : 377749549 ≤ 378011693) join_0_0 join_0_1

theorem join_1_1 : (twinPrimeSegment 378011693 378535981).card = 1791 := by
  simpa using combineTwinPrimeSegments (by decide : 378011693 ≤ 378273837)
    (by decide : 378273837 ≤ 378535981) join_0_2 join_0_3

theorem join_1_2 : (twinPrimeSegment 378535981 379060269).card = 1736 := by
  simpa using combineTwinPrimeSegments (by decide : 378535981 ≤ 378798125)
    (by decide : 378798125 ≤ 379060269) join_0_4 join_0_5

theorem join_1_3 : (twinPrimeSegment 379060269 379584557).card = 1747 := by
  simpa using combineTwinPrimeSegments (by decide : 379060269 ≤ 379322413)
    (by decide : 379322413 ≤ 379584557) join_0_6 join_0_7

theorem join_2_0 : (twinPrimeSegment 377487405 378535981).card = 3561 := by
  simpa using combineTwinPrimeSegments (by decide : 377487405 ≤ 378011693)
    (by decide : 378011693 ≤ 378535981) join_1_0 join_1_1

theorem join_2_1 : (twinPrimeSegment 378535981 379584557).card = 3483 := by
  simpa using combineTwinPrimeSegments (by decide : 378535981 ≤ 379060269)
    (by decide : 379060269 ≤ 379584557) join_1_2 join_1_3

theorem join_3_0 : (twinPrimeSegment 377487405 379584557).card = 7044 := by
  simpa using combineTwinPrimeSegments (by decide : 377487405 ≤ 378535981)
    (by decide : 378535981 ≤ 379584557) join_2_0 join_2_1

theorem total : (twinPrimeSegment 377487405 379584557).card = 7044 := join_3_0

end S180All
end Sude.GeneratedTwinScan
