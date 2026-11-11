import Sude.GeneratedTwinScan.S168C00
import Sude.GeneratedTwinScan.S168C01
import Sude.GeneratedTwinScan.S168C02
import Sude.GeneratedTwinScan.S168C03
import Sude.GeneratedTwinScan.S168C04
import Sude.GeneratedTwinScan.S168C05
import Sude.GeneratedTwinScan.S168C06
import Sude.GeneratedTwinScan.S168C07
import Sude.GeneratedTwinScan.S168C08
import Sude.GeneratedTwinScan.S168C09
import Sude.GeneratedTwinScan.S168C10
import Sude.GeneratedTwinScan.S168C11
import Sude.GeneratedTwinScan.S168C12
import Sude.GeneratedTwinScan.S168C13
import Sude.GeneratedTwinScan.S168C14
import Sude.GeneratedTwinScan.S168C15

/-! Combined FT source segment; Lean kernel check required. -/
namespace Sude.GeneratedTwinScan
namespace S168All

theorem join_0_0 : (twinPrimeSegment 352321581 352583725).card = 875 := by
  simpa using combineTwinPrimeSegments (by decide : 352321581 ≤ 352452653)
    (by decide : 352452653 ≤ 352583725) S168C00.total S168C01.total

theorem join_0_1 : (twinPrimeSegment 352583725 352845869).card = 842 := by
  simpa using combineTwinPrimeSegments (by decide : 352583725 ≤ 352714797)
    (by decide : 352714797 ≤ 352845869) S168C02.total S168C03.total

theorem join_0_2 : (twinPrimeSegment 352845869 353108013).card = 851 := by
  simpa using combineTwinPrimeSegments (by decide : 352845869 ≤ 352976941)
    (by decide : 352976941 ≤ 353108013) S168C04.total S168C05.total

theorem join_0_3 : (twinPrimeSegment 353108013 353370157).card = 871 := by
  simpa using combineTwinPrimeSegments (by decide : 353108013 ≤ 353239085)
    (by decide : 353239085 ≤ 353370157) S168C06.total S168C07.total

theorem join_0_4 : (twinPrimeSegment 353370157 353632301).card = 898 := by
  simpa using combineTwinPrimeSegments (by decide : 353370157 ≤ 353501229)
    (by decide : 353501229 ≤ 353632301) S168C08.total S168C09.total

theorem join_0_5 : (twinPrimeSegment 353632301 353894445).card = 932 := by
  simpa using combineTwinPrimeSegments (by decide : 353632301 ≤ 353763373)
    (by decide : 353763373 ≤ 353894445) S168C10.total S168C11.total

theorem join_0_6 : (twinPrimeSegment 353894445 354156589).card = 877 := by
  simpa using combineTwinPrimeSegments (by decide : 353894445 ≤ 354025517)
    (by decide : 354025517 ≤ 354156589) S168C12.total S168C13.total

theorem join_0_7 : (twinPrimeSegment 354156589 354418733).card = 914 := by
  simpa using combineTwinPrimeSegments (by decide : 354156589 ≤ 354287661)
    (by decide : 354287661 ≤ 354418733) S168C14.total S168C15.total

theorem join_1_0 : (twinPrimeSegment 352321581 352845869).card = 1717 := by
  simpa using combineTwinPrimeSegments (by decide : 352321581 ≤ 352583725)
    (by decide : 352583725 ≤ 352845869) join_0_0 join_0_1

theorem join_1_1 : (twinPrimeSegment 352845869 353370157).card = 1722 := by
  simpa using combineTwinPrimeSegments (by decide : 352845869 ≤ 353108013)
    (by decide : 353108013 ≤ 353370157) join_0_2 join_0_3

theorem join_1_2 : (twinPrimeSegment 353370157 353894445).card = 1830 := by
  simpa using combineTwinPrimeSegments (by decide : 353370157 ≤ 353632301)
    (by decide : 353632301 ≤ 353894445) join_0_4 join_0_5

theorem join_1_3 : (twinPrimeSegment 353894445 354418733).card = 1791 := by
  simpa using combineTwinPrimeSegments (by decide : 353894445 ≤ 354156589)
    (by decide : 354156589 ≤ 354418733) join_0_6 join_0_7

theorem join_2_0 : (twinPrimeSegment 352321581 353370157).card = 3439 := by
  simpa using combineTwinPrimeSegments (by decide : 352321581 ≤ 352845869)
    (by decide : 352845869 ≤ 353370157) join_1_0 join_1_1

theorem join_2_1 : (twinPrimeSegment 353370157 354418733).card = 3621 := by
  simpa using combineTwinPrimeSegments (by decide : 353370157 ≤ 353894445)
    (by decide : 353894445 ≤ 354418733) join_1_2 join_1_3

theorem join_3_0 : (twinPrimeSegment 352321581 354418733).card = 7060 := by
  simpa using combineTwinPrimeSegments (by decide : 352321581 ≤ 353370157)
    (by decide : 353370157 ≤ 354418733) join_2_0 join_2_1

theorem total : (twinPrimeSegment 352321581 354418733).card = 7060 := join_3_0

end S168All
end Sude.GeneratedTwinScan
