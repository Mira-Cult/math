import Sude.GeneratedTwinScan.S191C00
import Sude.GeneratedTwinScan.S191C01
import Sude.GeneratedTwinScan.S191C02
import Sude.GeneratedTwinScan.S191C03
import Sude.GeneratedTwinScan.S191C04
import Sude.GeneratedTwinScan.S191C05
import Sude.GeneratedTwinScan.S191C06
import Sude.GeneratedTwinScan.S191C07
import Sude.GeneratedTwinScan.S191C08
import Sude.GeneratedTwinScan.S191C09
import Sude.GeneratedTwinScan.S191C10
import Sude.GeneratedTwinScan.S191C11
import Sude.GeneratedTwinScan.S191C12
import Sude.GeneratedTwinScan.S191C13
import Sude.GeneratedTwinScan.S191C14
import Sude.GeneratedTwinScan.S191C15

/-! Combined FT source segment; Lean kernel check required. -/
namespace Sude.GeneratedTwinScan
namespace S191All

theorem join_0_0 : (twinPrimeSegment 400556077 400818221).card = 900 := by
  simpa using combineTwinPrimeSegments (by decide : 400556077 ≤ 400687149)
    (by decide : 400687149 ≤ 400818221) S191C00.total S191C01.total

theorem join_0_1 : (twinPrimeSegment 400818221 401080365).card = 873 := by
  simpa using combineTwinPrimeSegments (by decide : 400818221 ≤ 400949293)
    (by decide : 400949293 ≤ 401080365) S191C02.total S191C03.total

theorem join_0_2 : (twinPrimeSegment 401080365 401342509).card = 846 := by
  simpa using combineTwinPrimeSegments (by decide : 401080365 ≤ 401211437)
    (by decide : 401211437 ≤ 401342509) S191C04.total S191C05.total

theorem join_0_3 : (twinPrimeSegment 401342509 401604653).card = 886 := by
  simpa using combineTwinPrimeSegments (by decide : 401342509 ≤ 401473581)
    (by decide : 401473581 ≤ 401604653) S191C06.total S191C07.total

theorem join_0_4 : (twinPrimeSegment 401604653 401866797).card = 890 := by
  simpa using combineTwinPrimeSegments (by decide : 401604653 ≤ 401735725)
    (by decide : 401735725 ≤ 401866797) S191C08.total S191C09.total

theorem join_0_5 : (twinPrimeSegment 401866797 402128941).card = 888 := by
  simpa using combineTwinPrimeSegments (by decide : 401866797 ≤ 401997869)
    (by decide : 401997869 ≤ 402128941) S191C10.total S191C11.total

theorem join_0_6 : (twinPrimeSegment 402128941 402391085).card = 876 := by
  simpa using combineTwinPrimeSegments (by decide : 402128941 ≤ 402260013)
    (by decide : 402260013 ≤ 402391085) S191C12.total S191C13.total

theorem join_0_7 : (twinPrimeSegment 402391085 402653229).card = 909 := by
  simpa using combineTwinPrimeSegments (by decide : 402391085 ≤ 402522157)
    (by decide : 402522157 ≤ 402653229) S191C14.total S191C15.total

theorem join_1_0 : (twinPrimeSegment 400556077 401080365).card = 1773 := by
  simpa using combineTwinPrimeSegments (by decide : 400556077 ≤ 400818221)
    (by decide : 400818221 ≤ 401080365) join_0_0 join_0_1

theorem join_1_1 : (twinPrimeSegment 401080365 401604653).card = 1732 := by
  simpa using combineTwinPrimeSegments (by decide : 401080365 ≤ 401342509)
    (by decide : 401342509 ≤ 401604653) join_0_2 join_0_3

theorem join_1_2 : (twinPrimeSegment 401604653 402128941).card = 1778 := by
  simpa using combineTwinPrimeSegments (by decide : 401604653 ≤ 401866797)
    (by decide : 401866797 ≤ 402128941) join_0_4 join_0_5

theorem join_1_3 : (twinPrimeSegment 402128941 402653229).card = 1785 := by
  simpa using combineTwinPrimeSegments (by decide : 402128941 ≤ 402391085)
    (by decide : 402391085 ≤ 402653229) join_0_6 join_0_7

theorem join_2_0 : (twinPrimeSegment 400556077 401604653).card = 3505 := by
  simpa using combineTwinPrimeSegments (by decide : 400556077 ≤ 401080365)
    (by decide : 401080365 ≤ 401604653) join_1_0 join_1_1

theorem join_2_1 : (twinPrimeSegment 401604653 402653229).card = 3563 := by
  simpa using combineTwinPrimeSegments (by decide : 401604653 ≤ 402128941)
    (by decide : 402128941 ≤ 402653229) join_1_2 join_1_3

theorem join_3_0 : (twinPrimeSegment 400556077 402653229).card = 7068 := by
  simpa using combineTwinPrimeSegments (by decide : 400556077 ≤ 401604653)
    (by decide : 401604653 ≤ 402653229) join_2_0 join_2_1

theorem total : (twinPrimeSegment 400556077 402653229).card = 7068 := join_3_0

end S191All
end Sude.GeneratedTwinScan
