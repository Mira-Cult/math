import Sude.GeneratedTwinScan.S215C00
import Sude.GeneratedTwinScan.S215C01
import Sude.GeneratedTwinScan.S215C02
import Sude.GeneratedTwinScan.S215C03
import Sude.GeneratedTwinScan.S215C04
import Sude.GeneratedTwinScan.S215C05
import Sude.GeneratedTwinScan.S215C06
import Sude.GeneratedTwinScan.S215C07
import Sude.GeneratedTwinScan.S215C08
import Sude.GeneratedTwinScan.S215C09
import Sude.GeneratedTwinScan.S215C10
import Sude.GeneratedTwinScan.S215C11
import Sude.GeneratedTwinScan.S215C12
import Sude.GeneratedTwinScan.S215C13
import Sude.GeneratedTwinScan.S215C14
import Sude.GeneratedTwinScan.S215C15

/-! Combined FT source segment; Lean kernel check required. -/
namespace Sude.GeneratedTwinScan
namespace S215All

theorem join_0_0 : (twinPrimeSegment 450887725 451149869).card = 872 := by
  simpa using combineTwinPrimeSegments (by decide : 450887725 ≤ 451018797)
    (by decide : 451018797 ≤ 451149869) S215C00.total S215C01.total

theorem join_0_1 : (twinPrimeSegment 451149869 451412013).card = 885 := by
  simpa using combineTwinPrimeSegments (by decide : 451149869 ≤ 451280941)
    (by decide : 451280941 ≤ 451412013) S215C02.total S215C03.total

theorem join_0_2 : (twinPrimeSegment 451412013 451674157).card = 882 := by
  simpa using combineTwinPrimeSegments (by decide : 451412013 ≤ 451543085)
    (by decide : 451543085 ≤ 451674157) S215C04.total S215C05.total

theorem join_0_3 : (twinPrimeSegment 451674157 451936301).card = 847 := by
  simpa using combineTwinPrimeSegments (by decide : 451674157 ≤ 451805229)
    (by decide : 451805229 ≤ 451936301) S215C06.total S215C07.total

theorem join_0_4 : (twinPrimeSegment 451936301 452198445).card = 839 := by
  simpa using combineTwinPrimeSegments (by decide : 451936301 ≤ 452067373)
    (by decide : 452067373 ≤ 452198445) S215C08.total S215C09.total

theorem join_0_5 : (twinPrimeSegment 452198445 452460589).card = 886 := by
  simpa using combineTwinPrimeSegments (by decide : 452198445 ≤ 452329517)
    (by decide : 452329517 ≤ 452460589) S215C10.total S215C11.total

theorem join_0_6 : (twinPrimeSegment 452460589 452722733).card = 830 := by
  simpa using combineTwinPrimeSegments (by decide : 452460589 ≤ 452591661)
    (by decide : 452591661 ≤ 452722733) S215C12.total S215C13.total

theorem join_0_7 : (twinPrimeSegment 452722733 452984877).card = 879 := by
  simpa using combineTwinPrimeSegments (by decide : 452722733 ≤ 452853805)
    (by decide : 452853805 ≤ 452984877) S215C14.total S215C15.total

theorem join_1_0 : (twinPrimeSegment 450887725 451412013).card = 1757 := by
  simpa using combineTwinPrimeSegments (by decide : 450887725 ≤ 451149869)
    (by decide : 451149869 ≤ 451412013) join_0_0 join_0_1

theorem join_1_1 : (twinPrimeSegment 451412013 451936301).card = 1729 := by
  simpa using combineTwinPrimeSegments (by decide : 451412013 ≤ 451674157)
    (by decide : 451674157 ≤ 451936301) join_0_2 join_0_3

theorem join_1_2 : (twinPrimeSegment 451936301 452460589).card = 1725 := by
  simpa using combineTwinPrimeSegments (by decide : 451936301 ≤ 452198445)
    (by decide : 452198445 ≤ 452460589) join_0_4 join_0_5

theorem join_1_3 : (twinPrimeSegment 452460589 452984877).card = 1709 := by
  simpa using combineTwinPrimeSegments (by decide : 452460589 ≤ 452722733)
    (by decide : 452722733 ≤ 452984877) join_0_6 join_0_7

theorem join_2_0 : (twinPrimeSegment 450887725 451936301).card = 3486 := by
  simpa using combineTwinPrimeSegments (by decide : 450887725 ≤ 451412013)
    (by decide : 451412013 ≤ 451936301) join_1_0 join_1_1

theorem join_2_1 : (twinPrimeSegment 451936301 452984877).card = 3434 := by
  simpa using combineTwinPrimeSegments (by decide : 451936301 ≤ 452460589)
    (by decide : 452460589 ≤ 452984877) join_1_2 join_1_3

theorem join_3_0 : (twinPrimeSegment 450887725 452984877).card = 6920 := by
  simpa using combineTwinPrimeSegments (by decide : 450887725 ≤ 451936301)
    (by decide : 451936301 ≤ 452984877) join_2_0 join_2_1

theorem total : (twinPrimeSegment 450887725 452984877).card = 6920 := join_3_0

end S215All
end Sude.GeneratedTwinScan
