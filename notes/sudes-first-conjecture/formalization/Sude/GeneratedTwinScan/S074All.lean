import Sude.GeneratedTwinScan.S074C00
import Sude.GeneratedTwinScan.S074C01
import Sude.GeneratedTwinScan.S074C02
import Sude.GeneratedTwinScan.S074C03
import Sude.GeneratedTwinScan.S074C04
import Sude.GeneratedTwinScan.S074C05
import Sude.GeneratedTwinScan.S074C06
import Sude.GeneratedTwinScan.S074C07
import Sude.GeneratedTwinScan.S074C08
import Sude.GeneratedTwinScan.S074C09
import Sude.GeneratedTwinScan.S074C10
import Sude.GeneratedTwinScan.S074C11
import Sude.GeneratedTwinScan.S074C12
import Sude.GeneratedTwinScan.S074C13
import Sude.GeneratedTwinScan.S074C14
import Sude.GeneratedTwinScan.S074C15

/-! Combined FT source segment; Lean kernel check required. -/
namespace Sude.GeneratedTwinScan
namespace S074All

theorem join_0_0 : (twinPrimeSegment 155189293 155451437).card = 993 := by
  simpa using combineTwinPrimeSegments (by decide : 155189293 ≤ 155320365)
    (by decide : 155320365 ≤ 155451437) S074C00.total S074C01.total

theorem join_0_1 : (twinPrimeSegment 155451437 155713581).card = 1009 := by
  simpa using combineTwinPrimeSegments (by decide : 155451437 ≤ 155582509)
    (by decide : 155582509 ≤ 155713581) S074C02.total S074C03.total

theorem join_0_2 : (twinPrimeSegment 155713581 155975725).card = 988 := by
  simpa using combineTwinPrimeSegments (by decide : 155713581 ≤ 155844653)
    (by decide : 155844653 ≤ 155975725) S074C04.total S074C05.total

theorem join_0_3 : (twinPrimeSegment 155975725 156237869).card = 1009 := by
  simpa using combineTwinPrimeSegments (by decide : 155975725 ≤ 156106797)
    (by decide : 156106797 ≤ 156237869) S074C06.total S074C07.total

theorem join_0_4 : (twinPrimeSegment 156237869 156500013).card = 967 := by
  simpa using combineTwinPrimeSegments (by decide : 156237869 ≤ 156368941)
    (by decide : 156368941 ≤ 156500013) S074C08.total S074C09.total

theorem join_0_5 : (twinPrimeSegment 156500013 156762157).card = 975 := by
  simpa using combineTwinPrimeSegments (by decide : 156500013 ≤ 156631085)
    (by decide : 156631085 ≤ 156762157) S074C10.total S074C11.total

theorem join_0_6 : (twinPrimeSegment 156762157 157024301).card = 951 := by
  simpa using combineTwinPrimeSegments (by decide : 156762157 ≤ 156893229)
    (by decide : 156893229 ≤ 157024301) S074C12.total S074C13.total

theorem join_0_7 : (twinPrimeSegment 157024301 157286445).card = 974 := by
  simpa using combineTwinPrimeSegments (by decide : 157024301 ≤ 157155373)
    (by decide : 157155373 ≤ 157286445) S074C14.total S074C15.total

theorem join_1_0 : (twinPrimeSegment 155189293 155713581).card = 2002 := by
  simpa using combineTwinPrimeSegments (by decide : 155189293 ≤ 155451437)
    (by decide : 155451437 ≤ 155713581) join_0_0 join_0_1

theorem join_1_1 : (twinPrimeSegment 155713581 156237869).card = 1997 := by
  simpa using combineTwinPrimeSegments (by decide : 155713581 ≤ 155975725)
    (by decide : 155975725 ≤ 156237869) join_0_2 join_0_3

theorem join_1_2 : (twinPrimeSegment 156237869 156762157).card = 1942 := by
  simpa using combineTwinPrimeSegments (by decide : 156237869 ≤ 156500013)
    (by decide : 156500013 ≤ 156762157) join_0_4 join_0_5

theorem join_1_3 : (twinPrimeSegment 156762157 157286445).card = 1925 := by
  simpa using combineTwinPrimeSegments (by decide : 156762157 ≤ 157024301)
    (by decide : 157024301 ≤ 157286445) join_0_6 join_0_7

theorem join_2_0 : (twinPrimeSegment 155189293 156237869).card = 3999 := by
  simpa using combineTwinPrimeSegments (by decide : 155189293 ≤ 155713581)
    (by decide : 155713581 ≤ 156237869) join_1_0 join_1_1

theorem join_2_1 : (twinPrimeSegment 156237869 157286445).card = 3867 := by
  simpa using combineTwinPrimeSegments (by decide : 156237869 ≤ 156762157)
    (by decide : 156762157 ≤ 157286445) join_1_2 join_1_3

theorem join_3_0 : (twinPrimeSegment 155189293 157286445).card = 7866 := by
  simpa using combineTwinPrimeSegments (by decide : 155189293 ≤ 156237869)
    (by decide : 156237869 ≤ 157286445) join_2_0 join_2_1

theorem total : (twinPrimeSegment 155189293 157286445).card = 7866 := join_3_0

end S074All
end Sude.GeneratedTwinScan
