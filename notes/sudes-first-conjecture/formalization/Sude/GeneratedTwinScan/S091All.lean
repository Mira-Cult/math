import Sude.GeneratedTwinScan.S091C00
import Sude.GeneratedTwinScan.S091C01
import Sude.GeneratedTwinScan.S091C02
import Sude.GeneratedTwinScan.S091C03
import Sude.GeneratedTwinScan.S091C04
import Sude.GeneratedTwinScan.S091C05
import Sude.GeneratedTwinScan.S091C06
import Sude.GeneratedTwinScan.S091C07
import Sude.GeneratedTwinScan.S091C08
import Sude.GeneratedTwinScan.S091C09
import Sude.GeneratedTwinScan.S091C10
import Sude.GeneratedTwinScan.S091C11
import Sude.GeneratedTwinScan.S091C12
import Sude.GeneratedTwinScan.S091C13
import Sude.GeneratedTwinScan.S091C14
import Sude.GeneratedTwinScan.S091C15

/-! Combined FT source segment; Lean kernel check required. -/
namespace Sude.GeneratedTwinScan
namespace S091All

theorem join_0_0 : (twinPrimeSegment 190840877 191103021).card = 918 := by
  simpa using combineTwinPrimeSegments (by decide : 190840877 ≤ 190971949)
    (by decide : 190971949 ≤ 191103021) S091C00.total S091C01.total

theorem join_0_1 : (twinPrimeSegment 191103021 191365165).card = 953 := by
  simpa using combineTwinPrimeSegments (by decide : 191103021 ≤ 191234093)
    (by decide : 191234093 ≤ 191365165) S091C02.total S091C03.total

theorem join_0_2 : (twinPrimeSegment 191365165 191627309).card = 934 := by
  simpa using combineTwinPrimeSegments (by decide : 191365165 ≤ 191496237)
    (by decide : 191496237 ≤ 191627309) S091C04.total S091C05.total

theorem join_0_3 : (twinPrimeSegment 191627309 191889453).card = 978 := by
  simpa using combineTwinPrimeSegments (by decide : 191627309 ≤ 191758381)
    (by decide : 191758381 ≤ 191889453) S091C06.total S091C07.total

theorem join_0_4 : (twinPrimeSegment 191889453 192151597).card = 929 := by
  simpa using combineTwinPrimeSegments (by decide : 191889453 ≤ 192020525)
    (by decide : 192020525 ≤ 192151597) S091C08.total S091C09.total

theorem join_0_5 : (twinPrimeSegment 192151597 192413741).card = 957 := by
  simpa using combineTwinPrimeSegments (by decide : 192151597 ≤ 192282669)
    (by decide : 192282669 ≤ 192413741) S091C10.total S091C11.total

theorem join_0_6 : (twinPrimeSegment 192413741 192675885).card = 965 := by
  simpa using combineTwinPrimeSegments (by decide : 192413741 ≤ 192544813)
    (by decide : 192544813 ≤ 192675885) S091C12.total S091C13.total

theorem join_0_7 : (twinPrimeSegment 192675885 192938029).card = 941 := by
  simpa using combineTwinPrimeSegments (by decide : 192675885 ≤ 192806957)
    (by decide : 192806957 ≤ 192938029) S091C14.total S091C15.total

theorem join_1_0 : (twinPrimeSegment 190840877 191365165).card = 1871 := by
  simpa using combineTwinPrimeSegments (by decide : 190840877 ≤ 191103021)
    (by decide : 191103021 ≤ 191365165) join_0_0 join_0_1

theorem join_1_1 : (twinPrimeSegment 191365165 191889453).card = 1912 := by
  simpa using combineTwinPrimeSegments (by decide : 191365165 ≤ 191627309)
    (by decide : 191627309 ≤ 191889453) join_0_2 join_0_3

theorem join_1_2 : (twinPrimeSegment 191889453 192413741).card = 1886 := by
  simpa using combineTwinPrimeSegments (by decide : 191889453 ≤ 192151597)
    (by decide : 192151597 ≤ 192413741) join_0_4 join_0_5

theorem join_1_3 : (twinPrimeSegment 192413741 192938029).card = 1906 := by
  simpa using combineTwinPrimeSegments (by decide : 192413741 ≤ 192675885)
    (by decide : 192675885 ≤ 192938029) join_0_6 join_0_7

theorem join_2_0 : (twinPrimeSegment 190840877 191889453).card = 3783 := by
  simpa using combineTwinPrimeSegments (by decide : 190840877 ≤ 191365165)
    (by decide : 191365165 ≤ 191889453) join_1_0 join_1_1

theorem join_2_1 : (twinPrimeSegment 191889453 192938029).card = 3792 := by
  simpa using combineTwinPrimeSegments (by decide : 191889453 ≤ 192413741)
    (by decide : 192413741 ≤ 192938029) join_1_2 join_1_3

theorem join_3_0 : (twinPrimeSegment 190840877 192938029).card = 7575 := by
  simpa using combineTwinPrimeSegments (by decide : 190840877 ≤ 191889453)
    (by decide : 191889453 ≤ 192938029) join_2_0 join_2_1

theorem total : (twinPrimeSegment 190840877 192938029).card = 7575 := join_3_0

end S091All
end Sude.GeneratedTwinScan
