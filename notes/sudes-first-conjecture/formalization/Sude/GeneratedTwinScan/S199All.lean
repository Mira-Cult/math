import Sude.GeneratedTwinScan.S199C00
import Sude.GeneratedTwinScan.S199C01
import Sude.GeneratedTwinScan.S199C02
import Sude.GeneratedTwinScan.S199C03
import Sude.GeneratedTwinScan.S199C04
import Sude.GeneratedTwinScan.S199C05
import Sude.GeneratedTwinScan.S199C06
import Sude.GeneratedTwinScan.S199C07
import Sude.GeneratedTwinScan.S199C08
import Sude.GeneratedTwinScan.S199C09
import Sude.GeneratedTwinScan.S199C10
import Sude.GeneratedTwinScan.S199C11
import Sude.GeneratedTwinScan.S199C12
import Sude.GeneratedTwinScan.S199C13
import Sude.GeneratedTwinScan.S199C14
import Sude.GeneratedTwinScan.S199C15

/-! Combined FT source segment; Lean kernel check required. -/
namespace Sude.GeneratedTwinScan
namespace S199All

theorem join_0_0 : (twinPrimeSegment 417333293 417595437).card = 900 := by
  simpa using combineTwinPrimeSegments (by decide : 417333293 ≤ 417464365)
    (by decide : 417464365 ≤ 417595437) S199C00.total S199C01.total

theorem join_0_1 : (twinPrimeSegment 417595437 417857581).card = 867 := by
  simpa using combineTwinPrimeSegments (by decide : 417595437 ≤ 417726509)
    (by decide : 417726509 ≤ 417857581) S199C02.total S199C03.total

theorem join_0_2 : (twinPrimeSegment 417857581 418119725).card = 892 := by
  simpa using combineTwinPrimeSegments (by decide : 417857581 ≤ 417988653)
    (by decide : 417988653 ≤ 418119725) S199C04.total S199C05.total

theorem join_0_3 : (twinPrimeSegment 418119725 418381869).card = 910 := by
  simpa using combineTwinPrimeSegments (by decide : 418119725 ≤ 418250797)
    (by decide : 418250797 ≤ 418381869) S199C06.total S199C07.total

theorem join_0_4 : (twinPrimeSegment 418381869 418644013).card = 895 := by
  simpa using combineTwinPrimeSegments (by decide : 418381869 ≤ 418512941)
    (by decide : 418512941 ≤ 418644013) S199C08.total S199C09.total

theorem join_0_5 : (twinPrimeSegment 418644013 418906157).card = 902 := by
  simpa using combineTwinPrimeSegments (by decide : 418644013 ≤ 418775085)
    (by decide : 418775085 ≤ 418906157) S199C10.total S199C11.total

theorem join_0_6 : (twinPrimeSegment 418906157 419168301).card = 883 := by
  simpa using combineTwinPrimeSegments (by decide : 418906157 ≤ 419037229)
    (by decide : 419037229 ≤ 419168301) S199C12.total S199C13.total

theorem join_0_7 : (twinPrimeSegment 419168301 419430445).card = 871 := by
  simpa using combineTwinPrimeSegments (by decide : 419168301 ≤ 419299373)
    (by decide : 419299373 ≤ 419430445) S199C14.total S199C15.total

theorem join_1_0 : (twinPrimeSegment 417333293 417857581).card = 1767 := by
  simpa using combineTwinPrimeSegments (by decide : 417333293 ≤ 417595437)
    (by decide : 417595437 ≤ 417857581) join_0_0 join_0_1

theorem join_1_1 : (twinPrimeSegment 417857581 418381869).card = 1802 := by
  simpa using combineTwinPrimeSegments (by decide : 417857581 ≤ 418119725)
    (by decide : 418119725 ≤ 418381869) join_0_2 join_0_3

theorem join_1_2 : (twinPrimeSegment 418381869 418906157).card = 1797 := by
  simpa using combineTwinPrimeSegments (by decide : 418381869 ≤ 418644013)
    (by decide : 418644013 ≤ 418906157) join_0_4 join_0_5

theorem join_1_3 : (twinPrimeSegment 418906157 419430445).card = 1754 := by
  simpa using combineTwinPrimeSegments (by decide : 418906157 ≤ 419168301)
    (by decide : 419168301 ≤ 419430445) join_0_6 join_0_7

theorem join_2_0 : (twinPrimeSegment 417333293 418381869).card = 3569 := by
  simpa using combineTwinPrimeSegments (by decide : 417333293 ≤ 417857581)
    (by decide : 417857581 ≤ 418381869) join_1_0 join_1_1

theorem join_2_1 : (twinPrimeSegment 418381869 419430445).card = 3551 := by
  simpa using combineTwinPrimeSegments (by decide : 418381869 ≤ 418906157)
    (by decide : 418906157 ≤ 419430445) join_1_2 join_1_3

theorem join_3_0 : (twinPrimeSegment 417333293 419430445).card = 7120 := by
  simpa using combineTwinPrimeSegments (by decide : 417333293 ≤ 418381869)
    (by decide : 418381869 ≤ 419430445) join_2_0 join_2_1

theorem total : (twinPrimeSegment 417333293 419430445).card = 7120 := join_3_0

end S199All
end Sude.GeneratedTwinScan
