import Sude.GeneratedTwinScan.S216C00
import Sude.GeneratedTwinScan.S216C01
import Sude.GeneratedTwinScan.S216C02
import Sude.GeneratedTwinScan.S216C03
import Sude.GeneratedTwinScan.S216C04
import Sude.GeneratedTwinScan.S216C05
import Sude.GeneratedTwinScan.S216C06
import Sude.GeneratedTwinScan.S216C07
import Sude.GeneratedTwinScan.S216C08
import Sude.GeneratedTwinScan.S216C09
import Sude.GeneratedTwinScan.S216C10
import Sude.GeneratedTwinScan.S216C11
import Sude.GeneratedTwinScan.S216C12
import Sude.GeneratedTwinScan.S216C13
import Sude.GeneratedTwinScan.S216C14
import Sude.GeneratedTwinScan.S216C15

/-! Combined FT source segment; Lean kernel check required. -/
namespace Sude.GeneratedTwinScan
namespace S216All

theorem join_0_0 : (twinPrimeSegment 452984877 453247021).card = 872 := by
  simpa using combineTwinPrimeSegments (by decide : 452984877 ≤ 453115949)
    (by decide : 453115949 ≤ 453247021) S216C00.total S216C01.total

theorem join_0_1 : (twinPrimeSegment 453247021 453509165).card = 877 := by
  simpa using combineTwinPrimeSegments (by decide : 453247021 ≤ 453378093)
    (by decide : 453378093 ≤ 453509165) S216C02.total S216C03.total

theorem join_0_2 : (twinPrimeSegment 453509165 453771309).card = 912 := by
  simpa using combineTwinPrimeSegments (by decide : 453509165 ≤ 453640237)
    (by decide : 453640237 ≤ 453771309) S216C04.total S216C05.total

theorem join_0_3 : (twinPrimeSegment 453771309 454033453).card = 835 := by
  simpa using combineTwinPrimeSegments (by decide : 453771309 ≤ 453902381)
    (by decide : 453902381 ≤ 454033453) S216C06.total S216C07.total

theorem join_0_4 : (twinPrimeSegment 454033453 454295597).card = 876 := by
  simpa using combineTwinPrimeSegments (by decide : 454033453 ≤ 454164525)
    (by decide : 454164525 ≤ 454295597) S216C08.total S216C09.total

theorem join_0_5 : (twinPrimeSegment 454295597 454557741).card = 906 := by
  simpa using combineTwinPrimeSegments (by decide : 454295597 ≤ 454426669)
    (by decide : 454426669 ≤ 454557741) S216C10.total S216C11.total

theorem join_0_6 : (twinPrimeSegment 454557741 454819885).card = 894 := by
  simpa using combineTwinPrimeSegments (by decide : 454557741 ≤ 454688813)
    (by decide : 454688813 ≤ 454819885) S216C12.total S216C13.total

theorem join_0_7 : (twinPrimeSegment 454819885 455082029).card = 863 := by
  simpa using combineTwinPrimeSegments (by decide : 454819885 ≤ 454950957)
    (by decide : 454950957 ≤ 455082029) S216C14.total S216C15.total

theorem join_1_0 : (twinPrimeSegment 452984877 453509165).card = 1749 := by
  simpa using combineTwinPrimeSegments (by decide : 452984877 ≤ 453247021)
    (by decide : 453247021 ≤ 453509165) join_0_0 join_0_1

theorem join_1_1 : (twinPrimeSegment 453509165 454033453).card = 1747 := by
  simpa using combineTwinPrimeSegments (by decide : 453509165 ≤ 453771309)
    (by decide : 453771309 ≤ 454033453) join_0_2 join_0_3

theorem join_1_2 : (twinPrimeSegment 454033453 454557741).card = 1782 := by
  simpa using combineTwinPrimeSegments (by decide : 454033453 ≤ 454295597)
    (by decide : 454295597 ≤ 454557741) join_0_4 join_0_5

theorem join_1_3 : (twinPrimeSegment 454557741 455082029).card = 1757 := by
  simpa using combineTwinPrimeSegments (by decide : 454557741 ≤ 454819885)
    (by decide : 454819885 ≤ 455082029) join_0_6 join_0_7

theorem join_2_0 : (twinPrimeSegment 452984877 454033453).card = 3496 := by
  simpa using combineTwinPrimeSegments (by decide : 452984877 ≤ 453509165)
    (by decide : 453509165 ≤ 454033453) join_1_0 join_1_1

theorem join_2_1 : (twinPrimeSegment 454033453 455082029).card = 3539 := by
  simpa using combineTwinPrimeSegments (by decide : 454033453 ≤ 454557741)
    (by decide : 454557741 ≤ 455082029) join_1_2 join_1_3

theorem join_3_0 : (twinPrimeSegment 452984877 455082029).card = 7035 := by
  simpa using combineTwinPrimeSegments (by decide : 452984877 ≤ 454033453)
    (by decide : 454033453 ≤ 455082029) join_2_0 join_2_1

theorem total : (twinPrimeSegment 452984877 455082029).card = 7035 := join_3_0

end S216All
end Sude.GeneratedTwinScan
