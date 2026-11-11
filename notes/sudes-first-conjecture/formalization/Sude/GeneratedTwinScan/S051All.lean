import Sude.GeneratedTwinScan.S051C00
import Sude.GeneratedTwinScan.S051C01
import Sude.GeneratedTwinScan.S051C02
import Sude.GeneratedTwinScan.S051C03
import Sude.GeneratedTwinScan.S051C04
import Sude.GeneratedTwinScan.S051C05
import Sude.GeneratedTwinScan.S051C06
import Sude.GeneratedTwinScan.S051C07
import Sude.GeneratedTwinScan.S051C08
import Sude.GeneratedTwinScan.S051C09
import Sude.GeneratedTwinScan.S051C10
import Sude.GeneratedTwinScan.S051C11
import Sude.GeneratedTwinScan.S051C12
import Sude.GeneratedTwinScan.S051C13
import Sude.GeneratedTwinScan.S051C14
import Sude.GeneratedTwinScan.S051C15

/-! Combined FT source segment; Lean kernel check required. -/
namespace Sude.GeneratedTwinScan
namespace S051All

theorem join_0_0 : (twinPrimeSegment 106954797 107216941).card = 995 := by
  simpa using combineTwinPrimeSegments (by decide : 106954797 ≤ 107085869)
    (by decide : 107085869 ≤ 107216941) S051C00.total S051C01.total

theorem join_0_1 : (twinPrimeSegment 107216941 107479085).card = 1040 := by
  simpa using combineTwinPrimeSegments (by decide : 107216941 ≤ 107348013)
    (by decide : 107348013 ≤ 107479085) S051C02.total S051C03.total

theorem join_0_2 : (twinPrimeSegment 107479085 107741229).card = 1020 := by
  simpa using combineTwinPrimeSegments (by decide : 107479085 ≤ 107610157)
    (by decide : 107610157 ≤ 107741229) S051C04.total S051C05.total

theorem join_0_3 : (twinPrimeSegment 107741229 108003373).card = 981 := by
  simpa using combineTwinPrimeSegments (by decide : 107741229 ≤ 107872301)
    (by decide : 107872301 ≤ 108003373) S051C06.total S051C07.total

theorem join_0_4 : (twinPrimeSegment 108003373 108265517).card = 991 := by
  simpa using combineTwinPrimeSegments (by decide : 108003373 ≤ 108134445)
    (by decide : 108134445 ≤ 108265517) S051C08.total S051C09.total

theorem join_0_5 : (twinPrimeSegment 108265517 108527661).card = 1047 := by
  simpa using combineTwinPrimeSegments (by decide : 108265517 ≤ 108396589)
    (by decide : 108396589 ≤ 108527661) S051C10.total S051C11.total

theorem join_0_6 : (twinPrimeSegment 108527661 108789805).card = 991 := by
  simpa using combineTwinPrimeSegments (by decide : 108527661 ≤ 108658733)
    (by decide : 108658733 ≤ 108789805) S051C12.total S051C13.total

theorem join_0_7 : (twinPrimeSegment 108789805 109051949).card = 1047 := by
  simpa using combineTwinPrimeSegments (by decide : 108789805 ≤ 108920877)
    (by decide : 108920877 ≤ 109051949) S051C14.total S051C15.total

theorem join_1_0 : (twinPrimeSegment 106954797 107479085).card = 2035 := by
  simpa using combineTwinPrimeSegments (by decide : 106954797 ≤ 107216941)
    (by decide : 107216941 ≤ 107479085) join_0_0 join_0_1

theorem join_1_1 : (twinPrimeSegment 107479085 108003373).card = 2001 := by
  simpa using combineTwinPrimeSegments (by decide : 107479085 ≤ 107741229)
    (by decide : 107741229 ≤ 108003373) join_0_2 join_0_3

theorem join_1_2 : (twinPrimeSegment 108003373 108527661).card = 2038 := by
  simpa using combineTwinPrimeSegments (by decide : 108003373 ≤ 108265517)
    (by decide : 108265517 ≤ 108527661) join_0_4 join_0_5

theorem join_1_3 : (twinPrimeSegment 108527661 109051949).card = 2038 := by
  simpa using combineTwinPrimeSegments (by decide : 108527661 ≤ 108789805)
    (by decide : 108789805 ≤ 109051949) join_0_6 join_0_7

theorem join_2_0 : (twinPrimeSegment 106954797 108003373).card = 4036 := by
  simpa using combineTwinPrimeSegments (by decide : 106954797 ≤ 107479085)
    (by decide : 107479085 ≤ 108003373) join_1_0 join_1_1

theorem join_2_1 : (twinPrimeSegment 108003373 109051949).card = 4076 := by
  simpa using combineTwinPrimeSegments (by decide : 108003373 ≤ 108527661)
    (by decide : 108527661 ≤ 109051949) join_1_2 join_1_3

theorem join_3_0 : (twinPrimeSegment 106954797 109051949).card = 8112 := by
  simpa using combineTwinPrimeSegments (by decide : 106954797 ≤ 108003373)
    (by decide : 108003373 ≤ 109051949) join_2_0 join_2_1

theorem total : (twinPrimeSegment 106954797 109051949).card = 8112 := join_3_0

end S051All
end Sude.GeneratedTwinScan
