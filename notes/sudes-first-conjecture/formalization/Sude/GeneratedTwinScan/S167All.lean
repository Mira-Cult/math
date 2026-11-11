import Sude.GeneratedTwinScan.S167C00
import Sude.GeneratedTwinScan.S167C01
import Sude.GeneratedTwinScan.S167C02
import Sude.GeneratedTwinScan.S167C03
import Sude.GeneratedTwinScan.S167C04
import Sude.GeneratedTwinScan.S167C05
import Sude.GeneratedTwinScan.S167C06
import Sude.GeneratedTwinScan.S167C07
import Sude.GeneratedTwinScan.S167C08
import Sude.GeneratedTwinScan.S167C09
import Sude.GeneratedTwinScan.S167C10
import Sude.GeneratedTwinScan.S167C11
import Sude.GeneratedTwinScan.S167C12
import Sude.GeneratedTwinScan.S167C13
import Sude.GeneratedTwinScan.S167C14
import Sude.GeneratedTwinScan.S167C15

/-! Combined FT source segment; Lean kernel check required. -/
namespace Sude.GeneratedTwinScan
namespace S167All

theorem join_0_0 : (twinPrimeSegment 350224429 350486573).card = 865 := by
  simpa using combineTwinPrimeSegments (by decide : 350224429 ≤ 350355501)
    (by decide : 350355501 ≤ 350486573) S167C00.total S167C01.total

theorem join_0_1 : (twinPrimeSegment 350486573 350748717).card = 908 := by
  simpa using combineTwinPrimeSegments (by decide : 350486573 ≤ 350617645)
    (by decide : 350617645 ≤ 350748717) S167C02.total S167C03.total

theorem join_0_2 : (twinPrimeSegment 350748717 351010861).card = 887 := by
  simpa using combineTwinPrimeSegments (by decide : 350748717 ≤ 350879789)
    (by decide : 350879789 ≤ 351010861) S167C04.total S167C05.total

theorem join_0_3 : (twinPrimeSegment 351010861 351273005).card = 881 := by
  simpa using combineTwinPrimeSegments (by decide : 351010861 ≤ 351141933)
    (by decide : 351141933 ≤ 351273005) S167C06.total S167C07.total

theorem join_0_4 : (twinPrimeSegment 351273005 351535149).card = 914 := by
  simpa using combineTwinPrimeSegments (by decide : 351273005 ≤ 351404077)
    (by decide : 351404077 ≤ 351535149) S167C08.total S167C09.total

theorem join_0_5 : (twinPrimeSegment 351535149 351797293).card = 845 := by
  simpa using combineTwinPrimeSegments (by decide : 351535149 ≤ 351666221)
    (by decide : 351666221 ≤ 351797293) S167C10.total S167C11.total

theorem join_0_6 : (twinPrimeSegment 351797293 352059437).card = 836 := by
  simpa using combineTwinPrimeSegments (by decide : 351797293 ≤ 351928365)
    (by decide : 351928365 ≤ 352059437) S167C12.total S167C13.total

theorem join_0_7 : (twinPrimeSegment 352059437 352321581).card = 904 := by
  simpa using combineTwinPrimeSegments (by decide : 352059437 ≤ 352190509)
    (by decide : 352190509 ≤ 352321581) S167C14.total S167C15.total

theorem join_1_0 : (twinPrimeSegment 350224429 350748717).card = 1773 := by
  simpa using combineTwinPrimeSegments (by decide : 350224429 ≤ 350486573)
    (by decide : 350486573 ≤ 350748717) join_0_0 join_0_1

theorem join_1_1 : (twinPrimeSegment 350748717 351273005).card = 1768 := by
  simpa using combineTwinPrimeSegments (by decide : 350748717 ≤ 351010861)
    (by decide : 351010861 ≤ 351273005) join_0_2 join_0_3

theorem join_1_2 : (twinPrimeSegment 351273005 351797293).card = 1759 := by
  simpa using combineTwinPrimeSegments (by decide : 351273005 ≤ 351535149)
    (by decide : 351535149 ≤ 351797293) join_0_4 join_0_5

theorem join_1_3 : (twinPrimeSegment 351797293 352321581).card = 1740 := by
  simpa using combineTwinPrimeSegments (by decide : 351797293 ≤ 352059437)
    (by decide : 352059437 ≤ 352321581) join_0_6 join_0_7

theorem join_2_0 : (twinPrimeSegment 350224429 351273005).card = 3541 := by
  simpa using combineTwinPrimeSegments (by decide : 350224429 ≤ 350748717)
    (by decide : 350748717 ≤ 351273005) join_1_0 join_1_1

theorem join_2_1 : (twinPrimeSegment 351273005 352321581).card = 3499 := by
  simpa using combineTwinPrimeSegments (by decide : 351273005 ≤ 351797293)
    (by decide : 351797293 ≤ 352321581) join_1_2 join_1_3

theorem join_3_0 : (twinPrimeSegment 350224429 352321581).card = 7040 := by
  simpa using combineTwinPrimeSegments (by decide : 350224429 ≤ 351273005)
    (by decide : 351273005 ≤ 352321581) join_2_0 join_2_1

theorem total : (twinPrimeSegment 350224429 352321581).card = 7040 := join_3_0

end S167All
end Sude.GeneratedTwinScan
