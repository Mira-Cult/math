import Sude.GeneratedTwinScan.S094C00
import Sude.GeneratedTwinScan.S094C01
import Sude.GeneratedTwinScan.S094C02
import Sude.GeneratedTwinScan.S094C03
import Sude.GeneratedTwinScan.S094C04
import Sude.GeneratedTwinScan.S094C05
import Sude.GeneratedTwinScan.S094C06
import Sude.GeneratedTwinScan.S094C07
import Sude.GeneratedTwinScan.S094C08
import Sude.GeneratedTwinScan.S094C09
import Sude.GeneratedTwinScan.S094C10
import Sude.GeneratedTwinScan.S094C11
import Sude.GeneratedTwinScan.S094C12
import Sude.GeneratedTwinScan.S094C13
import Sude.GeneratedTwinScan.S094C14
import Sude.GeneratedTwinScan.S094C15

/-! Combined FT source segment; Lean kernel check required. -/
namespace Sude.GeneratedTwinScan
namespace S094All

theorem join_0_0 : (twinPrimeSegment 197132333 197394477).card = 971 := by
  simpa using combineTwinPrimeSegments (by decide : 197132333 ≤ 197263405)
    (by decide : 197263405 ≤ 197394477) S094C00.total S094C01.total

theorem join_0_1 : (twinPrimeSegment 197394477 197656621).card = 911 := by
  simpa using combineTwinPrimeSegments (by decide : 197394477 ≤ 197525549)
    (by decide : 197525549 ≤ 197656621) S094C02.total S094C03.total

theorem join_0_2 : (twinPrimeSegment 197656621 197918765).card = 942 := by
  simpa using combineTwinPrimeSegments (by decide : 197656621 ≤ 197787693)
    (by decide : 197787693 ≤ 197918765) S094C04.total S094C05.total

theorem join_0_3 : (twinPrimeSegment 197918765 198180909).card = 920 := by
  simpa using combineTwinPrimeSegments (by decide : 197918765 ≤ 198049837)
    (by decide : 198049837 ≤ 198180909) S094C06.total S094C07.total

theorem join_0_4 : (twinPrimeSegment 198180909 198443053).card = 1003 := by
  simpa using combineTwinPrimeSegments (by decide : 198180909 ≤ 198311981)
    (by decide : 198311981 ≤ 198443053) S094C08.total S094C09.total

theorem join_0_5 : (twinPrimeSegment 198443053 198705197).card = 957 := by
  simpa using combineTwinPrimeSegments (by decide : 198443053 ≤ 198574125)
    (by decide : 198574125 ≤ 198705197) S094C10.total S094C11.total

theorem join_0_6 : (twinPrimeSegment 198705197 198967341).card = 970 := by
  simpa using combineTwinPrimeSegments (by decide : 198705197 ≤ 198836269)
    (by decide : 198836269 ≤ 198967341) S094C12.total S094C13.total

theorem join_0_7 : (twinPrimeSegment 198967341 199229485).card = 937 := by
  simpa using combineTwinPrimeSegments (by decide : 198967341 ≤ 199098413)
    (by decide : 199098413 ≤ 199229485) S094C14.total S094C15.total

theorem join_1_0 : (twinPrimeSegment 197132333 197656621).card = 1882 := by
  simpa using combineTwinPrimeSegments (by decide : 197132333 ≤ 197394477)
    (by decide : 197394477 ≤ 197656621) join_0_0 join_0_1

theorem join_1_1 : (twinPrimeSegment 197656621 198180909).card = 1862 := by
  simpa using combineTwinPrimeSegments (by decide : 197656621 ≤ 197918765)
    (by decide : 197918765 ≤ 198180909) join_0_2 join_0_3

theorem join_1_2 : (twinPrimeSegment 198180909 198705197).card = 1960 := by
  simpa using combineTwinPrimeSegments (by decide : 198180909 ≤ 198443053)
    (by decide : 198443053 ≤ 198705197) join_0_4 join_0_5

theorem join_1_3 : (twinPrimeSegment 198705197 199229485).card = 1907 := by
  simpa using combineTwinPrimeSegments (by decide : 198705197 ≤ 198967341)
    (by decide : 198967341 ≤ 199229485) join_0_6 join_0_7

theorem join_2_0 : (twinPrimeSegment 197132333 198180909).card = 3744 := by
  simpa using combineTwinPrimeSegments (by decide : 197132333 ≤ 197656621)
    (by decide : 197656621 ≤ 198180909) join_1_0 join_1_1

theorem join_2_1 : (twinPrimeSegment 198180909 199229485).card = 3867 := by
  simpa using combineTwinPrimeSegments (by decide : 198180909 ≤ 198705197)
    (by decide : 198705197 ≤ 199229485) join_1_2 join_1_3

theorem join_3_0 : (twinPrimeSegment 197132333 199229485).card = 7611 := by
  simpa using combineTwinPrimeSegments (by decide : 197132333 ≤ 198180909)
    (by decide : 198180909 ≤ 199229485) join_2_0 join_2_1

theorem total : (twinPrimeSegment 197132333 199229485).card = 7611 := join_3_0

end S094All
end Sude.GeneratedTwinScan
