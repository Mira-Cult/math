import Sude.GeneratedTwinScan.S238C00
import Sude.GeneratedTwinScan.S238C01
import Sude.GeneratedTwinScan.S238C02
import Sude.GeneratedTwinScan.S238C03
import Sude.GeneratedTwinScan.S238C04
import Sude.GeneratedTwinScan.S238C05
import Sude.GeneratedTwinScan.S238C06
import Sude.GeneratedTwinScan.S238C07
import Sude.GeneratedTwinScan.S238C08
import Sude.GeneratedTwinScan.S238C09
import Sude.GeneratedTwinScan.S238C10
import Sude.GeneratedTwinScan.S238C11
import Sude.GeneratedTwinScan.S238C12
import Sude.GeneratedTwinScan.S238C13
import Sude.GeneratedTwinScan.S238C14
import Sude.GeneratedTwinScan.S238C15

/-! Combined FT source segment; Lean kernel check required. -/
namespace Sude.GeneratedTwinScan
namespace S238All

theorem join_0_0 : (twinPrimeSegment 499122221 499384365).card = 864 := by
  simpa using combineTwinPrimeSegments (by decide : 499122221 ≤ 499253293)
    (by decide : 499253293 ≤ 499384365) S238C00.total S238C01.total

theorem join_0_1 : (twinPrimeSegment 499384365 499646509).card = 885 := by
  simpa using combineTwinPrimeSegments (by decide : 499384365 ≤ 499515437)
    (by decide : 499515437 ≤ 499646509) S238C02.total S238C03.total

theorem join_0_2 : (twinPrimeSegment 499646509 499908653).card = 863 := by
  simpa using combineTwinPrimeSegments (by decide : 499646509 ≤ 499777581)
    (by decide : 499777581 ≤ 499908653) S238C04.total S238C05.total

theorem join_0_3 : (twinPrimeSegment 499908653 500170797).card = 862 := by
  simpa using combineTwinPrimeSegments (by decide : 499908653 ≤ 500039725)
    (by decide : 500039725 ≤ 500170797) S238C06.total S238C07.total

theorem join_0_4 : (twinPrimeSegment 500170797 500432941).card = 851 := by
  simpa using combineTwinPrimeSegments (by decide : 500170797 ≤ 500301869)
    (by decide : 500301869 ≤ 500432941) S238C08.total S238C09.total

theorem join_0_5 : (twinPrimeSegment 500432941 500695085).card = 861 := by
  simpa using combineTwinPrimeSegments (by decide : 500432941 ≤ 500564013)
    (by decide : 500564013 ≤ 500695085) S238C10.total S238C11.total

theorem join_0_6 : (twinPrimeSegment 500695085 500957229).card = 871 := by
  simpa using combineTwinPrimeSegments (by decide : 500695085 ≤ 500826157)
    (by decide : 500826157 ≤ 500957229) S238C12.total S238C13.total

theorem join_0_7 : (twinPrimeSegment 500957229 501219373).card = 838 := by
  simpa using combineTwinPrimeSegments (by decide : 500957229 ≤ 501088301)
    (by decide : 501088301 ≤ 501219373) S238C14.total S238C15.total

theorem join_1_0 : (twinPrimeSegment 499122221 499646509).card = 1749 := by
  simpa using combineTwinPrimeSegments (by decide : 499122221 ≤ 499384365)
    (by decide : 499384365 ≤ 499646509) join_0_0 join_0_1

theorem join_1_1 : (twinPrimeSegment 499646509 500170797).card = 1725 := by
  simpa using combineTwinPrimeSegments (by decide : 499646509 ≤ 499908653)
    (by decide : 499908653 ≤ 500170797) join_0_2 join_0_3

theorem join_1_2 : (twinPrimeSegment 500170797 500695085).card = 1712 := by
  simpa using combineTwinPrimeSegments (by decide : 500170797 ≤ 500432941)
    (by decide : 500432941 ≤ 500695085) join_0_4 join_0_5

theorem join_1_3 : (twinPrimeSegment 500695085 501219373).card = 1709 := by
  simpa using combineTwinPrimeSegments (by decide : 500695085 ≤ 500957229)
    (by decide : 500957229 ≤ 501219373) join_0_6 join_0_7

theorem join_2_0 : (twinPrimeSegment 499122221 500170797).card = 3474 := by
  simpa using combineTwinPrimeSegments (by decide : 499122221 ≤ 499646509)
    (by decide : 499646509 ≤ 500170797) join_1_0 join_1_1

theorem join_2_1 : (twinPrimeSegment 500170797 501219373).card = 3421 := by
  simpa using combineTwinPrimeSegments (by decide : 500170797 ≤ 500695085)
    (by decide : 500695085 ≤ 501219373) join_1_2 join_1_3

theorem join_3_0 : (twinPrimeSegment 499122221 501219373).card = 6895 := by
  simpa using combineTwinPrimeSegments (by decide : 499122221 ≤ 500170797)
    (by decide : 500170797 ≤ 501219373) join_2_0 join_2_1

theorem total : (twinPrimeSegment 499122221 501219373).card = 6895 := join_3_0

end S238All
end Sude.GeneratedTwinScan
