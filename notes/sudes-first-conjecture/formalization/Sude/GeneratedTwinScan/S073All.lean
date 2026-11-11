import Sude.GeneratedTwinScan.S073C00
import Sude.GeneratedTwinScan.S073C01
import Sude.GeneratedTwinScan.S073C02
import Sude.GeneratedTwinScan.S073C03
import Sude.GeneratedTwinScan.S073C04
import Sude.GeneratedTwinScan.S073C05
import Sude.GeneratedTwinScan.S073C06
import Sude.GeneratedTwinScan.S073C07
import Sude.GeneratedTwinScan.S073C08
import Sude.GeneratedTwinScan.S073C09
import Sude.GeneratedTwinScan.S073C10
import Sude.GeneratedTwinScan.S073C11
import Sude.GeneratedTwinScan.S073C12
import Sude.GeneratedTwinScan.S073C13
import Sude.GeneratedTwinScan.S073C14
import Sude.GeneratedTwinScan.S073C15

/-! Combined FT source segment; Lean kernel check required. -/
namespace Sude.GeneratedTwinScan
namespace S073All

theorem join_0_0 : (twinPrimeSegment 153092141 153354285).card = 982 := by
  simpa using combineTwinPrimeSegments (by decide : 153092141 ≤ 153223213)
    (by decide : 153223213 ≤ 153354285) S073C00.total S073C01.total

theorem join_0_1 : (twinPrimeSegment 153354285 153616429).card = 1020 := by
  simpa using combineTwinPrimeSegments (by decide : 153354285 ≤ 153485357)
    (by decide : 153485357 ≤ 153616429) S073C02.total S073C03.total

theorem join_0_2 : (twinPrimeSegment 153616429 153878573).card = 958 := by
  simpa using combineTwinPrimeSegments (by decide : 153616429 ≤ 153747501)
    (by decide : 153747501 ≤ 153878573) S073C04.total S073C05.total

theorem join_0_3 : (twinPrimeSegment 153878573 154140717).card = 989 := by
  simpa using combineTwinPrimeSegments (by decide : 153878573 ≤ 154009645)
    (by decide : 154009645 ≤ 154140717) S073C06.total S073C07.total

theorem join_0_4 : (twinPrimeSegment 154140717 154402861).card = 972 := by
  simpa using combineTwinPrimeSegments (by decide : 154140717 ≤ 154271789)
    (by decide : 154271789 ≤ 154402861) S073C08.total S073C09.total

theorem join_0_5 : (twinPrimeSegment 154402861 154665005).card = 908 := by
  simpa using combineTwinPrimeSegments (by decide : 154402861 ≤ 154533933)
    (by decide : 154533933 ≤ 154665005) S073C10.total S073C11.total

theorem join_0_6 : (twinPrimeSegment 154665005 154927149).card = 983 := by
  simpa using combineTwinPrimeSegments (by decide : 154665005 ≤ 154796077)
    (by decide : 154796077 ≤ 154927149) S073C12.total S073C13.total

theorem join_0_7 : (twinPrimeSegment 154927149 155189293).card = 987 := by
  simpa using combineTwinPrimeSegments (by decide : 154927149 ≤ 155058221)
    (by decide : 155058221 ≤ 155189293) S073C14.total S073C15.total

theorem join_1_0 : (twinPrimeSegment 153092141 153616429).card = 2002 := by
  simpa using combineTwinPrimeSegments (by decide : 153092141 ≤ 153354285)
    (by decide : 153354285 ≤ 153616429) join_0_0 join_0_1

theorem join_1_1 : (twinPrimeSegment 153616429 154140717).card = 1947 := by
  simpa using combineTwinPrimeSegments (by decide : 153616429 ≤ 153878573)
    (by decide : 153878573 ≤ 154140717) join_0_2 join_0_3

theorem join_1_2 : (twinPrimeSegment 154140717 154665005).card = 1880 := by
  simpa using combineTwinPrimeSegments (by decide : 154140717 ≤ 154402861)
    (by decide : 154402861 ≤ 154665005) join_0_4 join_0_5

theorem join_1_3 : (twinPrimeSegment 154665005 155189293).card = 1970 := by
  simpa using combineTwinPrimeSegments (by decide : 154665005 ≤ 154927149)
    (by decide : 154927149 ≤ 155189293) join_0_6 join_0_7

theorem join_2_0 : (twinPrimeSegment 153092141 154140717).card = 3949 := by
  simpa using combineTwinPrimeSegments (by decide : 153092141 ≤ 153616429)
    (by decide : 153616429 ≤ 154140717) join_1_0 join_1_1

theorem join_2_1 : (twinPrimeSegment 154140717 155189293).card = 3850 := by
  simpa using combineTwinPrimeSegments (by decide : 154140717 ≤ 154665005)
    (by decide : 154665005 ≤ 155189293) join_1_2 join_1_3

theorem join_3_0 : (twinPrimeSegment 153092141 155189293).card = 7799 := by
  simpa using combineTwinPrimeSegments (by decide : 153092141 ≤ 154140717)
    (by decide : 154140717 ≤ 155189293) join_2_0 join_2_1

theorem total : (twinPrimeSegment 153092141 155189293).card = 7799 := join_3_0

end S073All
end Sude.GeneratedTwinScan
