import Sude.GeneratedTwinScan.S012C00
import Sude.GeneratedTwinScan.S012C01
import Sude.GeneratedTwinScan.S012C02
import Sude.GeneratedTwinScan.S012C03
import Sude.GeneratedTwinScan.S012C04
import Sude.GeneratedTwinScan.S012C05
import Sude.GeneratedTwinScan.S012C06
import Sude.GeneratedTwinScan.S012C07
import Sude.GeneratedTwinScan.S012C08
import Sude.GeneratedTwinScan.S012C09
import Sude.GeneratedTwinScan.S012C10
import Sude.GeneratedTwinScan.S012C11
import Sude.GeneratedTwinScan.S012C12
import Sude.GeneratedTwinScan.S012C13
import Sude.GeneratedTwinScan.S012C14
import Sude.GeneratedTwinScan.S012C15

/-! Combined FT source segment; Lean kernel check required. -/
namespace Sude.GeneratedTwinScan
namespace S012All

theorem join_0_0 : (twinPrimeSegment 25165869 25428013).card = 1112 := by
  simpa using combineTwinPrimeSegments (by decide : 25165869 ≤ 25296941)
    (by decide : 25296941 ≤ 25428013) S012C00.total S012C01.total

theorem join_0_1 : (twinPrimeSegment 25428013 25690157).card = 1219 := by
  simpa using combineTwinPrimeSegments (by decide : 25428013 ≤ 25559085)
    (by decide : 25559085 ≤ 25690157) S012C02.total S012C03.total

theorem join_0_2 : (twinPrimeSegment 25690157 25952301).card = 1243 := by
  simpa using combineTwinPrimeSegments (by decide : 25690157 ≤ 25821229)
    (by decide : 25821229 ≤ 25952301) S012C04.total S012C05.total

theorem join_0_3 : (twinPrimeSegment 25952301 26214445).card = 1184 := by
  simpa using combineTwinPrimeSegments (by decide : 25952301 ≤ 26083373)
    (by decide : 26083373 ≤ 26214445) S012C06.total S012C07.total

theorem join_0_4 : (twinPrimeSegment 26214445 26476589).card = 1166 := by
  simpa using combineTwinPrimeSegments (by decide : 26214445 ≤ 26345517)
    (by decide : 26345517 ≤ 26476589) S012C08.total S012C09.total

theorem join_0_5 : (twinPrimeSegment 26476589 26738733).card = 1190 := by
  simpa using combineTwinPrimeSegments (by decide : 26476589 ≤ 26607661)
    (by decide : 26607661 ≤ 26738733) S012C10.total S012C11.total

theorem join_0_6 : (twinPrimeSegment 26738733 27000877).card = 1162 := by
  simpa using combineTwinPrimeSegments (by decide : 26738733 ≤ 26869805)
    (by decide : 26869805 ≤ 27000877) S012C12.total S012C13.total

theorem join_0_7 : (twinPrimeSegment 27000877 27263021).card = 1182 := by
  simpa using combineTwinPrimeSegments (by decide : 27000877 ≤ 27131949)
    (by decide : 27131949 ≤ 27263021) S012C14.total S012C15.total

theorem join_1_0 : (twinPrimeSegment 25165869 25690157).card = 2331 := by
  simpa using combineTwinPrimeSegments (by decide : 25165869 ≤ 25428013)
    (by decide : 25428013 ≤ 25690157) join_0_0 join_0_1

theorem join_1_1 : (twinPrimeSegment 25690157 26214445).card = 2427 := by
  simpa using combineTwinPrimeSegments (by decide : 25690157 ≤ 25952301)
    (by decide : 25952301 ≤ 26214445) join_0_2 join_0_3

theorem join_1_2 : (twinPrimeSegment 26214445 26738733).card = 2356 := by
  simpa using combineTwinPrimeSegments (by decide : 26214445 ≤ 26476589)
    (by decide : 26476589 ≤ 26738733) join_0_4 join_0_5

theorem join_1_3 : (twinPrimeSegment 26738733 27263021).card = 2344 := by
  simpa using combineTwinPrimeSegments (by decide : 26738733 ≤ 27000877)
    (by decide : 27000877 ≤ 27263021) join_0_6 join_0_7

theorem join_2_0 : (twinPrimeSegment 25165869 26214445).card = 4758 := by
  simpa using combineTwinPrimeSegments (by decide : 25165869 ≤ 25690157)
    (by decide : 25690157 ≤ 26214445) join_1_0 join_1_1

theorem join_2_1 : (twinPrimeSegment 26214445 27263021).card = 4700 := by
  simpa using combineTwinPrimeSegments (by decide : 26214445 ≤ 26738733)
    (by decide : 26738733 ≤ 27263021) join_1_2 join_1_3

theorem join_3_0 : (twinPrimeSegment 25165869 27263021).card = 9458 := by
  simpa using combineTwinPrimeSegments (by decide : 25165869 ≤ 26214445)
    (by decide : 26214445 ≤ 27263021) join_2_0 join_2_1

theorem total : (twinPrimeSegment 25165869 27263021).card = 9458 := join_3_0

end S012All
end Sude.GeneratedTwinScan
