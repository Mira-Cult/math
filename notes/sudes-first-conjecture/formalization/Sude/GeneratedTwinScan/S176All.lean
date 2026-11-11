import Sude.GeneratedTwinScan.S176C00
import Sude.GeneratedTwinScan.S176C01
import Sude.GeneratedTwinScan.S176C02
import Sude.GeneratedTwinScan.S176C03
import Sude.GeneratedTwinScan.S176C04
import Sude.GeneratedTwinScan.S176C05
import Sude.GeneratedTwinScan.S176C06
import Sude.GeneratedTwinScan.S176C07
import Sude.GeneratedTwinScan.S176C08
import Sude.GeneratedTwinScan.S176C09
import Sude.GeneratedTwinScan.S176C10
import Sude.GeneratedTwinScan.S176C11
import Sude.GeneratedTwinScan.S176C12
import Sude.GeneratedTwinScan.S176C13
import Sude.GeneratedTwinScan.S176C14
import Sude.GeneratedTwinScan.S176C15

/-! Combined FT source segment; Lean kernel check required. -/
namespace Sude.GeneratedTwinScan
namespace S176All

theorem join_0_0 : (twinPrimeSegment 369098797 369360941).card = 896 := by
  simpa using combineTwinPrimeSegments (by decide : 369098797 ≤ 369229869)
    (by decide : 369229869 ≤ 369360941) S176C00.total S176C01.total

theorem join_0_1 : (twinPrimeSegment 369360941 369623085).card = 857 := by
  simpa using combineTwinPrimeSegments (by decide : 369360941 ≤ 369492013)
    (by decide : 369492013 ≤ 369623085) S176C02.total S176C03.total

theorem join_0_2 : (twinPrimeSegment 369623085 369885229).card = 876 := by
  simpa using combineTwinPrimeSegments (by decide : 369623085 ≤ 369754157)
    (by decide : 369754157 ≤ 369885229) S176C04.total S176C05.total

theorem join_0_3 : (twinPrimeSegment 369885229 370147373).card = 896 := by
  simpa using combineTwinPrimeSegments (by decide : 369885229 ≤ 370016301)
    (by decide : 370016301 ≤ 370147373) S176C06.total S176C07.total

theorem join_0_4 : (twinPrimeSegment 370147373 370409517).card = 906 := by
  simpa using combineTwinPrimeSegments (by decide : 370147373 ≤ 370278445)
    (by decide : 370278445 ≤ 370409517) S176C08.total S176C09.total

theorem join_0_5 : (twinPrimeSegment 370409517 370671661).card = 889 := by
  simpa using combineTwinPrimeSegments (by decide : 370409517 ≤ 370540589)
    (by decide : 370540589 ≤ 370671661) S176C10.total S176C11.total

theorem join_0_6 : (twinPrimeSegment 370671661 370933805).card = 908 := by
  simpa using combineTwinPrimeSegments (by decide : 370671661 ≤ 370802733)
    (by decide : 370802733 ≤ 370933805) S176C12.total S176C13.total

theorem join_0_7 : (twinPrimeSegment 370933805 371195949).card = 892 := by
  simpa using combineTwinPrimeSegments (by decide : 370933805 ≤ 371064877)
    (by decide : 371064877 ≤ 371195949) S176C14.total S176C15.total

theorem join_1_0 : (twinPrimeSegment 369098797 369623085).card = 1753 := by
  simpa using combineTwinPrimeSegments (by decide : 369098797 ≤ 369360941)
    (by decide : 369360941 ≤ 369623085) join_0_0 join_0_1

theorem join_1_1 : (twinPrimeSegment 369623085 370147373).card = 1772 := by
  simpa using combineTwinPrimeSegments (by decide : 369623085 ≤ 369885229)
    (by decide : 369885229 ≤ 370147373) join_0_2 join_0_3

theorem join_1_2 : (twinPrimeSegment 370147373 370671661).card = 1795 := by
  simpa using combineTwinPrimeSegments (by decide : 370147373 ≤ 370409517)
    (by decide : 370409517 ≤ 370671661) join_0_4 join_0_5

theorem join_1_3 : (twinPrimeSegment 370671661 371195949).card = 1800 := by
  simpa using combineTwinPrimeSegments (by decide : 370671661 ≤ 370933805)
    (by decide : 370933805 ≤ 371195949) join_0_6 join_0_7

theorem join_2_0 : (twinPrimeSegment 369098797 370147373).card = 3525 := by
  simpa using combineTwinPrimeSegments (by decide : 369098797 ≤ 369623085)
    (by decide : 369623085 ≤ 370147373) join_1_0 join_1_1

theorem join_2_1 : (twinPrimeSegment 370147373 371195949).card = 3595 := by
  simpa using combineTwinPrimeSegments (by decide : 370147373 ≤ 370671661)
    (by decide : 370671661 ≤ 371195949) join_1_2 join_1_3

theorem join_3_0 : (twinPrimeSegment 369098797 371195949).card = 7120 := by
  simpa using combineTwinPrimeSegments (by decide : 369098797 ≤ 370147373)
    (by decide : 370147373 ≤ 371195949) join_2_0 join_2_1

theorem total : (twinPrimeSegment 369098797 371195949).card = 7120 := join_3_0

end S176All
end Sude.GeneratedTwinScan
