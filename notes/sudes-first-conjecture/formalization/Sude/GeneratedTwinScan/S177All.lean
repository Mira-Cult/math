import Sude.GeneratedTwinScan.S177C00
import Sude.GeneratedTwinScan.S177C01
import Sude.GeneratedTwinScan.S177C02
import Sude.GeneratedTwinScan.S177C03
import Sude.GeneratedTwinScan.S177C04
import Sude.GeneratedTwinScan.S177C05
import Sude.GeneratedTwinScan.S177C06
import Sude.GeneratedTwinScan.S177C07
import Sude.GeneratedTwinScan.S177C08
import Sude.GeneratedTwinScan.S177C09
import Sude.GeneratedTwinScan.S177C10
import Sude.GeneratedTwinScan.S177C11
import Sude.GeneratedTwinScan.S177C12
import Sude.GeneratedTwinScan.S177C13
import Sude.GeneratedTwinScan.S177C14
import Sude.GeneratedTwinScan.S177C15

/-! Combined FT source segment; Lean kernel check required. -/
namespace Sude.GeneratedTwinScan
namespace S177All

theorem join_0_0 : (twinPrimeSegment 371195949 371458093).card = 855 := by
  simpa using combineTwinPrimeSegments (by decide : 371195949 ≤ 371327021)
    (by decide : 371327021 ≤ 371458093) S177C00.total S177C01.total

theorem join_0_1 : (twinPrimeSegment 371458093 371720237).card = 848 := by
  simpa using combineTwinPrimeSegments (by decide : 371458093 ≤ 371589165)
    (by decide : 371589165 ≤ 371720237) S177C02.total S177C03.total

theorem join_0_2 : (twinPrimeSegment 371720237 371982381).card = 936 := by
  simpa using combineTwinPrimeSegments (by decide : 371720237 ≤ 371851309)
    (by decide : 371851309 ≤ 371982381) S177C04.total S177C05.total

theorem join_0_3 : (twinPrimeSegment 371982381 372244525).card = 892 := by
  simpa using combineTwinPrimeSegments (by decide : 371982381 ≤ 372113453)
    (by decide : 372113453 ≤ 372244525) S177C06.total S177C07.total

theorem join_0_4 : (twinPrimeSegment 372244525 372506669).card = 899 := by
  simpa using combineTwinPrimeSegments (by decide : 372244525 ≤ 372375597)
    (by decide : 372375597 ≤ 372506669) S177C08.total S177C09.total

theorem join_0_5 : (twinPrimeSegment 372506669 372768813).card = 887 := by
  simpa using combineTwinPrimeSegments (by decide : 372506669 ≤ 372637741)
    (by decide : 372637741 ≤ 372768813) S177C10.total S177C11.total

theorem join_0_6 : (twinPrimeSegment 372768813 373030957).card = 923 := by
  simpa using combineTwinPrimeSegments (by decide : 372768813 ≤ 372899885)
    (by decide : 372899885 ≤ 373030957) S177C12.total S177C13.total

theorem join_0_7 : (twinPrimeSegment 373030957 373293101).card = 896 := by
  simpa using combineTwinPrimeSegments (by decide : 373030957 ≤ 373162029)
    (by decide : 373162029 ≤ 373293101) S177C14.total S177C15.total

theorem join_1_0 : (twinPrimeSegment 371195949 371720237).card = 1703 := by
  simpa using combineTwinPrimeSegments (by decide : 371195949 ≤ 371458093)
    (by decide : 371458093 ≤ 371720237) join_0_0 join_0_1

theorem join_1_1 : (twinPrimeSegment 371720237 372244525).card = 1828 := by
  simpa using combineTwinPrimeSegments (by decide : 371720237 ≤ 371982381)
    (by decide : 371982381 ≤ 372244525) join_0_2 join_0_3

theorem join_1_2 : (twinPrimeSegment 372244525 372768813).card = 1786 := by
  simpa using combineTwinPrimeSegments (by decide : 372244525 ≤ 372506669)
    (by decide : 372506669 ≤ 372768813) join_0_4 join_0_5

theorem join_1_3 : (twinPrimeSegment 372768813 373293101).card = 1819 := by
  simpa using combineTwinPrimeSegments (by decide : 372768813 ≤ 373030957)
    (by decide : 373030957 ≤ 373293101) join_0_6 join_0_7

theorem join_2_0 : (twinPrimeSegment 371195949 372244525).card = 3531 := by
  simpa using combineTwinPrimeSegments (by decide : 371195949 ≤ 371720237)
    (by decide : 371720237 ≤ 372244525) join_1_0 join_1_1

theorem join_2_1 : (twinPrimeSegment 372244525 373293101).card = 3605 := by
  simpa using combineTwinPrimeSegments (by decide : 372244525 ≤ 372768813)
    (by decide : 372768813 ≤ 373293101) join_1_2 join_1_3

theorem join_3_0 : (twinPrimeSegment 371195949 373293101).card = 7136 := by
  simpa using combineTwinPrimeSegments (by decide : 371195949 ≤ 372244525)
    (by decide : 372244525 ≤ 373293101) join_2_0 join_2_1

theorem total : (twinPrimeSegment 371195949 373293101).card = 7136 := join_3_0

end S177All
end Sude.GeneratedTwinScan
