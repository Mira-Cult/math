import Sude.GeneratedTwinScan.S175C00
import Sude.GeneratedTwinScan.S175C01
import Sude.GeneratedTwinScan.S175C02
import Sude.GeneratedTwinScan.S175C03
import Sude.GeneratedTwinScan.S175C04
import Sude.GeneratedTwinScan.S175C05
import Sude.GeneratedTwinScan.S175C06
import Sude.GeneratedTwinScan.S175C07
import Sude.GeneratedTwinScan.S175C08
import Sude.GeneratedTwinScan.S175C09
import Sude.GeneratedTwinScan.S175C10
import Sude.GeneratedTwinScan.S175C11
import Sude.GeneratedTwinScan.S175C12
import Sude.GeneratedTwinScan.S175C13
import Sude.GeneratedTwinScan.S175C14
import Sude.GeneratedTwinScan.S175C15

/-! Combined FT source segment; Lean kernel check required. -/
namespace Sude.GeneratedTwinScan
namespace S175All

theorem join_0_0 : (twinPrimeSegment 367001645 367263789).card = 906 := by
  simpa using combineTwinPrimeSegments (by decide : 367001645 ≤ 367132717)
    (by decide : 367132717 ≤ 367263789) S175C00.total S175C01.total

theorem join_0_1 : (twinPrimeSegment 367263789 367525933).card = 883 := by
  simpa using combineTwinPrimeSegments (by decide : 367263789 ≤ 367394861)
    (by decide : 367394861 ≤ 367525933) S175C02.total S175C03.total

theorem join_0_2 : (twinPrimeSegment 367525933 367788077).card = 929 := by
  simpa using combineTwinPrimeSegments (by decide : 367525933 ≤ 367657005)
    (by decide : 367657005 ≤ 367788077) S175C04.total S175C05.total

theorem join_0_3 : (twinPrimeSegment 367788077 368050221).card = 856 := by
  simpa using combineTwinPrimeSegments (by decide : 367788077 ≤ 367919149)
    (by decide : 367919149 ≤ 368050221) S175C06.total S175C07.total

theorem join_0_4 : (twinPrimeSegment 368050221 368312365).card = 888 := by
  simpa using combineTwinPrimeSegments (by decide : 368050221 ≤ 368181293)
    (by decide : 368181293 ≤ 368312365) S175C08.total S175C09.total

theorem join_0_5 : (twinPrimeSegment 368312365 368574509).card = 855 := by
  simpa using combineTwinPrimeSegments (by decide : 368312365 ≤ 368443437)
    (by decide : 368443437 ≤ 368574509) S175C10.total S175C11.total

theorem join_0_6 : (twinPrimeSegment 368574509 368836653).card = 867 := by
  simpa using combineTwinPrimeSegments (by decide : 368574509 ≤ 368705581)
    (by decide : 368705581 ≤ 368836653) S175C12.total S175C13.total

theorem join_0_7 : (twinPrimeSegment 368836653 369098797).card = 865 := by
  simpa using combineTwinPrimeSegments (by decide : 368836653 ≤ 368967725)
    (by decide : 368967725 ≤ 369098797) S175C14.total S175C15.total

theorem join_1_0 : (twinPrimeSegment 367001645 367525933).card = 1789 := by
  simpa using combineTwinPrimeSegments (by decide : 367001645 ≤ 367263789)
    (by decide : 367263789 ≤ 367525933) join_0_0 join_0_1

theorem join_1_1 : (twinPrimeSegment 367525933 368050221).card = 1785 := by
  simpa using combineTwinPrimeSegments (by decide : 367525933 ≤ 367788077)
    (by decide : 367788077 ≤ 368050221) join_0_2 join_0_3

theorem join_1_2 : (twinPrimeSegment 368050221 368574509).card = 1743 := by
  simpa using combineTwinPrimeSegments (by decide : 368050221 ≤ 368312365)
    (by decide : 368312365 ≤ 368574509) join_0_4 join_0_5

theorem join_1_3 : (twinPrimeSegment 368574509 369098797).card = 1732 := by
  simpa using combineTwinPrimeSegments (by decide : 368574509 ≤ 368836653)
    (by decide : 368836653 ≤ 369098797) join_0_6 join_0_7

theorem join_2_0 : (twinPrimeSegment 367001645 368050221).card = 3574 := by
  simpa using combineTwinPrimeSegments (by decide : 367001645 ≤ 367525933)
    (by decide : 367525933 ≤ 368050221) join_1_0 join_1_1

theorem join_2_1 : (twinPrimeSegment 368050221 369098797).card = 3475 := by
  simpa using combineTwinPrimeSegments (by decide : 368050221 ≤ 368574509)
    (by decide : 368574509 ≤ 369098797) join_1_2 join_1_3

theorem join_3_0 : (twinPrimeSegment 367001645 369098797).card = 7049 := by
  simpa using combineTwinPrimeSegments (by decide : 367001645 ≤ 368050221)
    (by decide : 368050221 ≤ 369098797) join_2_0 join_2_1

theorem total : (twinPrimeSegment 367001645 369098797).card = 7049 := join_3_0

end S175All
end Sude.GeneratedTwinScan
