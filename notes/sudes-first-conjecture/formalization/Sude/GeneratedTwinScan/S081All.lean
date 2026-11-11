import Sude.GeneratedTwinScan.S081C00
import Sude.GeneratedTwinScan.S081C01
import Sude.GeneratedTwinScan.S081C02
import Sude.GeneratedTwinScan.S081C03
import Sude.GeneratedTwinScan.S081C04
import Sude.GeneratedTwinScan.S081C05
import Sude.GeneratedTwinScan.S081C06
import Sude.GeneratedTwinScan.S081C07
import Sude.GeneratedTwinScan.S081C08
import Sude.GeneratedTwinScan.S081C09
import Sude.GeneratedTwinScan.S081C10
import Sude.GeneratedTwinScan.S081C11
import Sude.GeneratedTwinScan.S081C12
import Sude.GeneratedTwinScan.S081C13
import Sude.GeneratedTwinScan.S081C14
import Sude.GeneratedTwinScan.S081C15

/-! Combined FT source segment; Lean kernel check required. -/
namespace Sude.GeneratedTwinScan
namespace S081All

theorem join_0_0 : (twinPrimeSegment 169869357 170131501).card = 981 := by
  simpa using combineTwinPrimeSegments (by decide : 169869357 ≤ 170000429)
    (by decide : 170000429 ≤ 170131501) S081C00.total S081C01.total

theorem join_0_1 : (twinPrimeSegment 170131501 170393645).card = 906 := by
  simpa using combineTwinPrimeSegments (by decide : 170131501 ≤ 170262573)
    (by decide : 170262573 ≤ 170393645) S081C02.total S081C03.total

theorem join_0_2 : (twinPrimeSegment 170393645 170655789).card = 939 := by
  simpa using combineTwinPrimeSegments (by decide : 170393645 ≤ 170524717)
    (by decide : 170524717 ≤ 170655789) S081C04.total S081C05.total

theorem join_0_3 : (twinPrimeSegment 170655789 170917933).card = 982 := by
  simpa using combineTwinPrimeSegments (by decide : 170655789 ≤ 170786861)
    (by decide : 170786861 ≤ 170917933) S081C06.total S081C07.total

theorem join_0_4 : (twinPrimeSegment 170917933 171180077).card = 988 := by
  simpa using combineTwinPrimeSegments (by decide : 170917933 ≤ 171049005)
    (by decide : 171049005 ≤ 171180077) S081C08.total S081C09.total

theorem join_0_5 : (twinPrimeSegment 171180077 171442221).card = 925 := by
  simpa using combineTwinPrimeSegments (by decide : 171180077 ≤ 171311149)
    (by decide : 171311149 ≤ 171442221) S081C10.total S081C11.total

theorem join_0_6 : (twinPrimeSegment 171442221 171704365).card = 950 := by
  simpa using combineTwinPrimeSegments (by decide : 171442221 ≤ 171573293)
    (by decide : 171573293 ≤ 171704365) S081C12.total S081C13.total

theorem join_0_7 : (twinPrimeSegment 171704365 171966509).card = 988 := by
  simpa using combineTwinPrimeSegments (by decide : 171704365 ≤ 171835437)
    (by decide : 171835437 ≤ 171966509) S081C14.total S081C15.total

theorem join_1_0 : (twinPrimeSegment 169869357 170393645).card = 1887 := by
  simpa using combineTwinPrimeSegments (by decide : 169869357 ≤ 170131501)
    (by decide : 170131501 ≤ 170393645) join_0_0 join_0_1

theorem join_1_1 : (twinPrimeSegment 170393645 170917933).card = 1921 := by
  simpa using combineTwinPrimeSegments (by decide : 170393645 ≤ 170655789)
    (by decide : 170655789 ≤ 170917933) join_0_2 join_0_3

theorem join_1_2 : (twinPrimeSegment 170917933 171442221).card = 1913 := by
  simpa using combineTwinPrimeSegments (by decide : 170917933 ≤ 171180077)
    (by decide : 171180077 ≤ 171442221) join_0_4 join_0_5

theorem join_1_3 : (twinPrimeSegment 171442221 171966509).card = 1938 := by
  simpa using combineTwinPrimeSegments (by decide : 171442221 ≤ 171704365)
    (by decide : 171704365 ≤ 171966509) join_0_6 join_0_7

theorem join_2_0 : (twinPrimeSegment 169869357 170917933).card = 3808 := by
  simpa using combineTwinPrimeSegments (by decide : 169869357 ≤ 170393645)
    (by decide : 170393645 ≤ 170917933) join_1_0 join_1_1

theorem join_2_1 : (twinPrimeSegment 170917933 171966509).card = 3851 := by
  simpa using combineTwinPrimeSegments (by decide : 170917933 ≤ 171442221)
    (by decide : 171442221 ≤ 171966509) join_1_2 join_1_3

theorem join_3_0 : (twinPrimeSegment 169869357 171966509).card = 7659 := by
  simpa using combineTwinPrimeSegments (by decide : 169869357 ≤ 170917933)
    (by decide : 170917933 ≤ 171966509) join_2_0 join_2_1

theorem total : (twinPrimeSegment 169869357 171966509).card = 7659 := join_3_0

end S081All
end Sude.GeneratedTwinScan
