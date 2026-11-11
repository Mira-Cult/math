import Sude.GeneratedTwinScan.S148C00
import Sude.GeneratedTwinScan.S148C01
import Sude.GeneratedTwinScan.S148C02
import Sude.GeneratedTwinScan.S148C03
import Sude.GeneratedTwinScan.S148C04
import Sude.GeneratedTwinScan.S148C05
import Sude.GeneratedTwinScan.S148C06
import Sude.GeneratedTwinScan.S148C07
import Sude.GeneratedTwinScan.S148C08
import Sude.GeneratedTwinScan.S148C09
import Sude.GeneratedTwinScan.S148C10
import Sude.GeneratedTwinScan.S148C11
import Sude.GeneratedTwinScan.S148C12
import Sude.GeneratedTwinScan.S148C13
import Sude.GeneratedTwinScan.S148C14
import Sude.GeneratedTwinScan.S148C15

/-! Combined FT source segment; Lean kernel check required. -/
namespace Sude.GeneratedTwinScan
namespace S148All

theorem join_0_0 : (twinPrimeSegment 310378541 310640685).card = 921 := by
  simpa using combineTwinPrimeSegments (by decide : 310378541 ≤ 310509613)
    (by decide : 310509613 ≤ 310640685) S148C00.total S148C01.total

theorem join_0_1 : (twinPrimeSegment 310640685 310902829).card = 871 := by
  simpa using combineTwinPrimeSegments (by decide : 310640685 ≤ 310771757)
    (by decide : 310771757 ≤ 310902829) S148C02.total S148C03.total

theorem join_0_2 : (twinPrimeSegment 310902829 311164973).card = 932 := by
  simpa using combineTwinPrimeSegments (by decide : 310902829 ≤ 311033901)
    (by decide : 311033901 ≤ 311164973) S148C04.total S148C05.total

theorem join_0_3 : (twinPrimeSegment 311164973 311427117).card = 880 := by
  simpa using combineTwinPrimeSegments (by decide : 311164973 ≤ 311296045)
    (by decide : 311296045 ≤ 311427117) S148C06.total S148C07.total

theorem join_0_4 : (twinPrimeSegment 311427117 311689261).card = 934 := by
  simpa using combineTwinPrimeSegments (by decide : 311427117 ≤ 311558189)
    (by decide : 311558189 ≤ 311689261) S148C08.total S148C09.total

theorem join_0_5 : (twinPrimeSegment 311689261 311951405).card = 904 := by
  simpa using combineTwinPrimeSegments (by decide : 311689261 ≤ 311820333)
    (by decide : 311820333 ≤ 311951405) S148C10.total S148C11.total

theorem join_0_6 : (twinPrimeSegment 311951405 312213549).card = 925 := by
  simpa using combineTwinPrimeSegments (by decide : 311951405 ≤ 312082477)
    (by decide : 312082477 ≤ 312213549) S148C12.total S148C13.total

theorem join_0_7 : (twinPrimeSegment 312213549 312475693).card = 924 := by
  simpa using combineTwinPrimeSegments (by decide : 312213549 ≤ 312344621)
    (by decide : 312344621 ≤ 312475693) S148C14.total S148C15.total

theorem join_1_0 : (twinPrimeSegment 310378541 310902829).card = 1792 := by
  simpa using combineTwinPrimeSegments (by decide : 310378541 ≤ 310640685)
    (by decide : 310640685 ≤ 310902829) join_0_0 join_0_1

theorem join_1_1 : (twinPrimeSegment 310902829 311427117).card = 1812 := by
  simpa using combineTwinPrimeSegments (by decide : 310902829 ≤ 311164973)
    (by decide : 311164973 ≤ 311427117) join_0_2 join_0_3

theorem join_1_2 : (twinPrimeSegment 311427117 311951405).card = 1838 := by
  simpa using combineTwinPrimeSegments (by decide : 311427117 ≤ 311689261)
    (by decide : 311689261 ≤ 311951405) join_0_4 join_0_5

theorem join_1_3 : (twinPrimeSegment 311951405 312475693).card = 1849 := by
  simpa using combineTwinPrimeSegments (by decide : 311951405 ≤ 312213549)
    (by decide : 312213549 ≤ 312475693) join_0_6 join_0_7

theorem join_2_0 : (twinPrimeSegment 310378541 311427117).card = 3604 := by
  simpa using combineTwinPrimeSegments (by decide : 310378541 ≤ 310902829)
    (by decide : 310902829 ≤ 311427117) join_1_0 join_1_1

theorem join_2_1 : (twinPrimeSegment 311427117 312475693).card = 3687 := by
  simpa using combineTwinPrimeSegments (by decide : 311427117 ≤ 311951405)
    (by decide : 311951405 ≤ 312475693) join_1_2 join_1_3

theorem join_3_0 : (twinPrimeSegment 310378541 312475693).card = 7291 := by
  simpa using combineTwinPrimeSegments (by decide : 310378541 ≤ 311427117)
    (by decide : 311427117 ≤ 312475693) join_2_0 join_2_1

theorem total : (twinPrimeSegment 310378541 312475693).card = 7291 := join_3_0

end S148All
end Sude.GeneratedTwinScan
