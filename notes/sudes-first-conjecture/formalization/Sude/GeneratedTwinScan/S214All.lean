import Sude.GeneratedTwinScan.S214C00
import Sude.GeneratedTwinScan.S214C01
import Sude.GeneratedTwinScan.S214C02
import Sude.GeneratedTwinScan.S214C03
import Sude.GeneratedTwinScan.S214C04
import Sude.GeneratedTwinScan.S214C05
import Sude.GeneratedTwinScan.S214C06
import Sude.GeneratedTwinScan.S214C07
import Sude.GeneratedTwinScan.S214C08
import Sude.GeneratedTwinScan.S214C09
import Sude.GeneratedTwinScan.S214C10
import Sude.GeneratedTwinScan.S214C11
import Sude.GeneratedTwinScan.S214C12
import Sude.GeneratedTwinScan.S214C13
import Sude.GeneratedTwinScan.S214C14
import Sude.GeneratedTwinScan.S214C15

/-! Combined FT source segment; Lean kernel check required. -/
namespace Sude.GeneratedTwinScan
namespace S214All

theorem join_0_0 : (twinPrimeSegment 448790573 449052717).card = 884 := by
  simpa using combineTwinPrimeSegments (by decide : 448790573 ≤ 448921645)
    (by decide : 448921645 ≤ 449052717) S214C00.total S214C01.total

theorem join_0_1 : (twinPrimeSegment 449052717 449314861).card = 871 := by
  simpa using combineTwinPrimeSegments (by decide : 449052717 ≤ 449183789)
    (by decide : 449183789 ≤ 449314861) S214C02.total S214C03.total

theorem join_0_2 : (twinPrimeSegment 449314861 449577005).card = 912 := by
  simpa using combineTwinPrimeSegments (by decide : 449314861 ≤ 449445933)
    (by decide : 449445933 ≤ 449577005) S214C04.total S214C05.total

theorem join_0_3 : (twinPrimeSegment 449577005 449839149).card = 896 := by
  simpa using combineTwinPrimeSegments (by decide : 449577005 ≤ 449708077)
    (by decide : 449708077 ≤ 449839149) S214C06.total S214C07.total

theorem join_0_4 : (twinPrimeSegment 449839149 450101293).card = 811 := by
  simpa using combineTwinPrimeSegments (by decide : 449839149 ≤ 449970221)
    (by decide : 449970221 ≤ 450101293) S214C08.total S214C09.total

theorem join_0_5 : (twinPrimeSegment 450101293 450363437).card = 879 := by
  simpa using combineTwinPrimeSegments (by decide : 450101293 ≤ 450232365)
    (by decide : 450232365 ≤ 450363437) S214C10.total S214C11.total

theorem join_0_6 : (twinPrimeSegment 450363437 450625581).card = 867 := by
  simpa using combineTwinPrimeSegments (by decide : 450363437 ≤ 450494509)
    (by decide : 450494509 ≤ 450625581) S214C12.total S214C13.total

theorem join_0_7 : (twinPrimeSegment 450625581 450887725).card = 871 := by
  simpa using combineTwinPrimeSegments (by decide : 450625581 ≤ 450756653)
    (by decide : 450756653 ≤ 450887725) S214C14.total S214C15.total

theorem join_1_0 : (twinPrimeSegment 448790573 449314861).card = 1755 := by
  simpa using combineTwinPrimeSegments (by decide : 448790573 ≤ 449052717)
    (by decide : 449052717 ≤ 449314861) join_0_0 join_0_1

theorem join_1_1 : (twinPrimeSegment 449314861 449839149).card = 1808 := by
  simpa using combineTwinPrimeSegments (by decide : 449314861 ≤ 449577005)
    (by decide : 449577005 ≤ 449839149) join_0_2 join_0_3

theorem join_1_2 : (twinPrimeSegment 449839149 450363437).card = 1690 := by
  simpa using combineTwinPrimeSegments (by decide : 449839149 ≤ 450101293)
    (by decide : 450101293 ≤ 450363437) join_0_4 join_0_5

theorem join_1_3 : (twinPrimeSegment 450363437 450887725).card = 1738 := by
  simpa using combineTwinPrimeSegments (by decide : 450363437 ≤ 450625581)
    (by decide : 450625581 ≤ 450887725) join_0_6 join_0_7

theorem join_2_0 : (twinPrimeSegment 448790573 449839149).card = 3563 := by
  simpa using combineTwinPrimeSegments (by decide : 448790573 ≤ 449314861)
    (by decide : 449314861 ≤ 449839149) join_1_0 join_1_1

theorem join_2_1 : (twinPrimeSegment 449839149 450887725).card = 3428 := by
  simpa using combineTwinPrimeSegments (by decide : 449839149 ≤ 450363437)
    (by decide : 450363437 ≤ 450887725) join_1_2 join_1_3

theorem join_3_0 : (twinPrimeSegment 448790573 450887725).card = 6991 := by
  simpa using combineTwinPrimeSegments (by decide : 448790573 ≤ 449839149)
    (by decide : 449839149 ≤ 450887725) join_2_0 join_2_1

theorem total : (twinPrimeSegment 448790573 450887725).card = 6991 := join_3_0

end S214All
end Sude.GeneratedTwinScan
