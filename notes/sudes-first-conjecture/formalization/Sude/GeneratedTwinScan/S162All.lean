import Sude.GeneratedTwinScan.S162C00
import Sude.GeneratedTwinScan.S162C01
import Sude.GeneratedTwinScan.S162C02
import Sude.GeneratedTwinScan.S162C03
import Sude.GeneratedTwinScan.S162C04
import Sude.GeneratedTwinScan.S162C05
import Sude.GeneratedTwinScan.S162C06
import Sude.GeneratedTwinScan.S162C07
import Sude.GeneratedTwinScan.S162C08
import Sude.GeneratedTwinScan.S162C09
import Sude.GeneratedTwinScan.S162C10
import Sude.GeneratedTwinScan.S162C11
import Sude.GeneratedTwinScan.S162C12
import Sude.GeneratedTwinScan.S162C13
import Sude.GeneratedTwinScan.S162C14
import Sude.GeneratedTwinScan.S162C15

/-! Combined FT source segment; Lean kernel check required. -/
namespace Sude.GeneratedTwinScan
namespace S162All

theorem join_0_0 : (twinPrimeSegment 339738669 340000813).card = 892 := by
  simpa using combineTwinPrimeSegments (by decide : 339738669 ≤ 339869741)
    (by decide : 339869741 ≤ 340000813) S162C00.total S162C01.total

theorem join_0_1 : (twinPrimeSegment 340000813 340262957).card = 958 := by
  simpa using combineTwinPrimeSegments (by decide : 340000813 ≤ 340131885)
    (by decide : 340131885 ≤ 340262957) S162C02.total S162C03.total

theorem join_0_2 : (twinPrimeSegment 340262957 340525101).card = 910 := by
  simpa using combineTwinPrimeSegments (by decide : 340262957 ≤ 340394029)
    (by decide : 340394029 ≤ 340525101) S162C04.total S162C05.total

theorem join_0_3 : (twinPrimeSegment 340525101 340787245).card = 887 := by
  simpa using combineTwinPrimeSegments (by decide : 340525101 ≤ 340656173)
    (by decide : 340656173 ≤ 340787245) S162C06.total S162C07.total

theorem join_0_4 : (twinPrimeSegment 340787245 341049389).card = 849 := by
  simpa using combineTwinPrimeSegments (by decide : 340787245 ≤ 340918317)
    (by decide : 340918317 ≤ 341049389) S162C08.total S162C09.total

theorem join_0_5 : (twinPrimeSegment 341049389 341311533).card = 836 := by
  simpa using combineTwinPrimeSegments (by decide : 341049389 ≤ 341180461)
    (by decide : 341180461 ≤ 341311533) S162C10.total S162C11.total

theorem join_0_6 : (twinPrimeSegment 341311533 341573677).card = 941 := by
  simpa using combineTwinPrimeSegments (by decide : 341311533 ≤ 341442605)
    (by decide : 341442605 ≤ 341573677) S162C12.total S162C13.total

theorem join_0_7 : (twinPrimeSegment 341573677 341835821).card = 879 := by
  simpa using combineTwinPrimeSegments (by decide : 341573677 ≤ 341704749)
    (by decide : 341704749 ≤ 341835821) S162C14.total S162C15.total

theorem join_1_0 : (twinPrimeSegment 339738669 340262957).card = 1850 := by
  simpa using combineTwinPrimeSegments (by decide : 339738669 ≤ 340000813)
    (by decide : 340000813 ≤ 340262957) join_0_0 join_0_1

theorem join_1_1 : (twinPrimeSegment 340262957 340787245).card = 1797 := by
  simpa using combineTwinPrimeSegments (by decide : 340262957 ≤ 340525101)
    (by decide : 340525101 ≤ 340787245) join_0_2 join_0_3

theorem join_1_2 : (twinPrimeSegment 340787245 341311533).card = 1685 := by
  simpa using combineTwinPrimeSegments (by decide : 340787245 ≤ 341049389)
    (by decide : 341049389 ≤ 341311533) join_0_4 join_0_5

theorem join_1_3 : (twinPrimeSegment 341311533 341835821).card = 1820 := by
  simpa using combineTwinPrimeSegments (by decide : 341311533 ≤ 341573677)
    (by decide : 341573677 ≤ 341835821) join_0_6 join_0_7

theorem join_2_0 : (twinPrimeSegment 339738669 340787245).card = 3647 := by
  simpa using combineTwinPrimeSegments (by decide : 339738669 ≤ 340262957)
    (by decide : 340262957 ≤ 340787245) join_1_0 join_1_1

theorem join_2_1 : (twinPrimeSegment 340787245 341835821).card = 3505 := by
  simpa using combineTwinPrimeSegments (by decide : 340787245 ≤ 341311533)
    (by decide : 341311533 ≤ 341835821) join_1_2 join_1_3

theorem join_3_0 : (twinPrimeSegment 339738669 341835821).card = 7152 := by
  simpa using combineTwinPrimeSegments (by decide : 339738669 ≤ 340787245)
    (by decide : 340787245 ≤ 341835821) join_2_0 join_2_1

theorem total : (twinPrimeSegment 339738669 341835821).card = 7152 := join_3_0

end S162All
end Sude.GeneratedTwinScan
