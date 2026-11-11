import Sude.GeneratedTwinScan.S103C00
import Sude.GeneratedTwinScan.S103C01
import Sude.GeneratedTwinScan.S103C02
import Sude.GeneratedTwinScan.S103C03
import Sude.GeneratedTwinScan.S103C04
import Sude.GeneratedTwinScan.S103C05
import Sude.GeneratedTwinScan.S103C06
import Sude.GeneratedTwinScan.S103C07
import Sude.GeneratedTwinScan.S103C08
import Sude.GeneratedTwinScan.S103C09
import Sude.GeneratedTwinScan.S103C10
import Sude.GeneratedTwinScan.S103C11
import Sude.GeneratedTwinScan.S103C12
import Sude.GeneratedTwinScan.S103C13
import Sude.GeneratedTwinScan.S103C14
import Sude.GeneratedTwinScan.S103C15

/-! Combined FT source segment; Lean kernel check required. -/
namespace Sude.GeneratedTwinScan
namespace S103All

theorem join_0_0 : (twinPrimeSegment 216006701 216268845).card = 925 := by
  simpa using combineTwinPrimeSegments (by decide : 216006701 ≤ 216137773)
    (by decide : 216137773 ≤ 216268845) S103C00.total S103C01.total

theorem join_0_1 : (twinPrimeSegment 216268845 216530989).card = 927 := by
  simpa using combineTwinPrimeSegments (by decide : 216268845 ≤ 216399917)
    (by decide : 216399917 ≤ 216530989) S103C02.total S103C03.total

theorem join_0_2 : (twinPrimeSegment 216530989 216793133).card = 903 := by
  simpa using combineTwinPrimeSegments (by decide : 216530989 ≤ 216662061)
    (by decide : 216662061 ≤ 216793133) S103C04.total S103C05.total

theorem join_0_3 : (twinPrimeSegment 216793133 217055277).card = 947 := by
  simpa using combineTwinPrimeSegments (by decide : 216793133 ≤ 216924205)
    (by decide : 216924205 ≤ 217055277) S103C06.total S103C07.total

theorem join_0_4 : (twinPrimeSegment 217055277 217317421).card = 907 := by
  simpa using combineTwinPrimeSegments (by decide : 217055277 ≤ 217186349)
    (by decide : 217186349 ≤ 217317421) S103C08.total S103C09.total

theorem join_0_5 : (twinPrimeSegment 217317421 217579565).card = 932 := by
  simpa using combineTwinPrimeSegments (by decide : 217317421 ≤ 217448493)
    (by decide : 217448493 ≤ 217579565) S103C10.total S103C11.total

theorem join_0_6 : (twinPrimeSegment 217579565 217841709).card = 907 := by
  simpa using combineTwinPrimeSegments (by decide : 217579565 ≤ 217710637)
    (by decide : 217710637 ≤ 217841709) S103C12.total S103C13.total

theorem join_0_7 : (twinPrimeSegment 217841709 218103853).card = 913 := by
  simpa using combineTwinPrimeSegments (by decide : 217841709 ≤ 217972781)
    (by decide : 217972781 ≤ 218103853) S103C14.total S103C15.total

theorem join_1_0 : (twinPrimeSegment 216006701 216530989).card = 1852 := by
  simpa using combineTwinPrimeSegments (by decide : 216006701 ≤ 216268845)
    (by decide : 216268845 ≤ 216530989) join_0_0 join_0_1

theorem join_1_1 : (twinPrimeSegment 216530989 217055277).card = 1850 := by
  simpa using combineTwinPrimeSegments (by decide : 216530989 ≤ 216793133)
    (by decide : 216793133 ≤ 217055277) join_0_2 join_0_3

theorem join_1_2 : (twinPrimeSegment 217055277 217579565).card = 1839 := by
  simpa using combineTwinPrimeSegments (by decide : 217055277 ≤ 217317421)
    (by decide : 217317421 ≤ 217579565) join_0_4 join_0_5

theorem join_1_3 : (twinPrimeSegment 217579565 218103853).card = 1820 := by
  simpa using combineTwinPrimeSegments (by decide : 217579565 ≤ 217841709)
    (by decide : 217841709 ≤ 218103853) join_0_6 join_0_7

theorem join_2_0 : (twinPrimeSegment 216006701 217055277).card = 3702 := by
  simpa using combineTwinPrimeSegments (by decide : 216006701 ≤ 216530989)
    (by decide : 216530989 ≤ 217055277) join_1_0 join_1_1

theorem join_2_1 : (twinPrimeSegment 217055277 218103853).card = 3659 := by
  simpa using combineTwinPrimeSegments (by decide : 217055277 ≤ 217579565)
    (by decide : 217579565 ≤ 218103853) join_1_2 join_1_3

theorem join_3_0 : (twinPrimeSegment 216006701 218103853).card = 7361 := by
  simpa using combineTwinPrimeSegments (by decide : 216006701 ≤ 217055277)
    (by decide : 217055277 ≤ 218103853) join_2_0 join_2_1

theorem total : (twinPrimeSegment 216006701 218103853).card = 7361 := join_3_0

end S103All
end Sude.GeneratedTwinScan
