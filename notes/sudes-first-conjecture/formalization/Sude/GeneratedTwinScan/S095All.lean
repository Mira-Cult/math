import Sude.GeneratedTwinScan.S095C00
import Sude.GeneratedTwinScan.S095C01
import Sude.GeneratedTwinScan.S095C02
import Sude.GeneratedTwinScan.S095C03
import Sude.GeneratedTwinScan.S095C04
import Sude.GeneratedTwinScan.S095C05
import Sude.GeneratedTwinScan.S095C06
import Sude.GeneratedTwinScan.S095C07
import Sude.GeneratedTwinScan.S095C08
import Sude.GeneratedTwinScan.S095C09
import Sude.GeneratedTwinScan.S095C10
import Sude.GeneratedTwinScan.S095C11
import Sude.GeneratedTwinScan.S095C12
import Sude.GeneratedTwinScan.S095C13
import Sude.GeneratedTwinScan.S095C14
import Sude.GeneratedTwinScan.S095C15

/-! Combined FT source segment; Lean kernel check required. -/
namespace Sude.GeneratedTwinScan
namespace S095All

theorem join_0_0 : (twinPrimeSegment 199229485 199491629).card = 976 := by
  simpa using combineTwinPrimeSegments (by decide : 199229485 ≤ 199360557)
    (by decide : 199360557 ≤ 199491629) S095C00.total S095C01.total

theorem join_0_1 : (twinPrimeSegment 199491629 199753773).card = 998 := by
  simpa using combineTwinPrimeSegments (by decide : 199491629 ≤ 199622701)
    (by decide : 199622701 ≤ 199753773) S095C02.total S095C03.total

theorem join_0_2 : (twinPrimeSegment 199753773 200015917).card = 980 := by
  simpa using combineTwinPrimeSegments (by decide : 199753773 ≤ 199884845)
    (by decide : 199884845 ≤ 200015917) S095C04.total S095C05.total

theorem join_0_3 : (twinPrimeSegment 200015917 200278061).card = 964 := by
  simpa using combineTwinPrimeSegments (by decide : 200015917 ≤ 200146989)
    (by decide : 200146989 ≤ 200278061) S095C06.total S095C07.total

theorem join_0_4 : (twinPrimeSegment 200278061 200540205).card = 912 := by
  simpa using combineTwinPrimeSegments (by decide : 200278061 ≤ 200409133)
    (by decide : 200409133 ≤ 200540205) S095C08.total S095C09.total

theorem join_0_5 : (twinPrimeSegment 200540205 200802349).card = 926 := by
  simpa using combineTwinPrimeSegments (by decide : 200540205 ≤ 200671277)
    (by decide : 200671277 ≤ 200802349) S095C10.total S095C11.total

theorem join_0_6 : (twinPrimeSegment 200802349 201064493).card = 973 := by
  simpa using combineTwinPrimeSegments (by decide : 200802349 ≤ 200933421)
    (by decide : 200933421 ≤ 201064493) S095C12.total S095C13.total

theorem join_0_7 : (twinPrimeSegment 201064493 201326637).card = 954 := by
  simpa using combineTwinPrimeSegments (by decide : 201064493 ≤ 201195565)
    (by decide : 201195565 ≤ 201326637) S095C14.total S095C15.total

theorem join_1_0 : (twinPrimeSegment 199229485 199753773).card = 1974 := by
  simpa using combineTwinPrimeSegments (by decide : 199229485 ≤ 199491629)
    (by decide : 199491629 ≤ 199753773) join_0_0 join_0_1

theorem join_1_1 : (twinPrimeSegment 199753773 200278061).card = 1944 := by
  simpa using combineTwinPrimeSegments (by decide : 199753773 ≤ 200015917)
    (by decide : 200015917 ≤ 200278061) join_0_2 join_0_3

theorem join_1_2 : (twinPrimeSegment 200278061 200802349).card = 1838 := by
  simpa using combineTwinPrimeSegments (by decide : 200278061 ≤ 200540205)
    (by decide : 200540205 ≤ 200802349) join_0_4 join_0_5

theorem join_1_3 : (twinPrimeSegment 200802349 201326637).card = 1927 := by
  simpa using combineTwinPrimeSegments (by decide : 200802349 ≤ 201064493)
    (by decide : 201064493 ≤ 201326637) join_0_6 join_0_7

theorem join_2_0 : (twinPrimeSegment 199229485 200278061).card = 3918 := by
  simpa using combineTwinPrimeSegments (by decide : 199229485 ≤ 199753773)
    (by decide : 199753773 ≤ 200278061) join_1_0 join_1_1

theorem join_2_1 : (twinPrimeSegment 200278061 201326637).card = 3765 := by
  simpa using combineTwinPrimeSegments (by decide : 200278061 ≤ 200802349)
    (by decide : 200802349 ≤ 201326637) join_1_2 join_1_3

theorem join_3_0 : (twinPrimeSegment 199229485 201326637).card = 7683 := by
  simpa using combineTwinPrimeSegments (by decide : 199229485 ≤ 200278061)
    (by decide : 200278061 ≤ 201326637) join_2_0 join_2_1

theorem total : (twinPrimeSegment 199229485 201326637).card = 7683 := join_3_0

end S095All
end Sude.GeneratedTwinScan
