import Sude.GeneratedTwinScan.S160C00
import Sude.GeneratedTwinScan.S160C01
import Sude.GeneratedTwinScan.S160C02
import Sude.GeneratedTwinScan.S160C03
import Sude.GeneratedTwinScan.S160C04
import Sude.GeneratedTwinScan.S160C05
import Sude.GeneratedTwinScan.S160C06
import Sude.GeneratedTwinScan.S160C07
import Sude.GeneratedTwinScan.S160C08
import Sude.GeneratedTwinScan.S160C09
import Sude.GeneratedTwinScan.S160C10
import Sude.GeneratedTwinScan.S160C11
import Sude.GeneratedTwinScan.S160C12
import Sude.GeneratedTwinScan.S160C13
import Sude.GeneratedTwinScan.S160C14
import Sude.GeneratedTwinScan.S160C15

/-! Combined FT source segment; Lean kernel check required. -/
namespace Sude.GeneratedTwinScan
namespace S160All

theorem join_0_0 : (twinPrimeSegment 335544365 335806509).card = 877 := by
  simpa using combineTwinPrimeSegments (by decide : 335544365 ≤ 335675437)
    (by decide : 335675437 ≤ 335806509) S160C00.total S160C01.total

theorem join_0_1 : (twinPrimeSegment 335806509 336068653).card = 917 := by
  simpa using combineTwinPrimeSegments (by decide : 335806509 ≤ 335937581)
    (by decide : 335937581 ≤ 336068653) S160C02.total S160C03.total

theorem join_0_2 : (twinPrimeSegment 336068653 336330797).card = 919 := by
  simpa using combineTwinPrimeSegments (by decide : 336068653 ≤ 336199725)
    (by decide : 336199725 ≤ 336330797) S160C04.total S160C05.total

theorem join_0_3 : (twinPrimeSegment 336330797 336592941).card = 897 := by
  simpa using combineTwinPrimeSegments (by decide : 336330797 ≤ 336461869)
    (by decide : 336461869 ≤ 336592941) S160C06.total S160C07.total

theorem join_0_4 : (twinPrimeSegment 336592941 336855085).card = 908 := by
  simpa using combineTwinPrimeSegments (by decide : 336592941 ≤ 336724013)
    (by decide : 336724013 ≤ 336855085) S160C08.total S160C09.total

theorem join_0_5 : (twinPrimeSegment 336855085 337117229).card = 896 := by
  simpa using combineTwinPrimeSegments (by decide : 336855085 ≤ 336986157)
    (by decide : 336986157 ≤ 337117229) S160C10.total S160C11.total

theorem join_0_6 : (twinPrimeSegment 337117229 337379373).card = 907 := by
  simpa using combineTwinPrimeSegments (by decide : 337117229 ≤ 337248301)
    (by decide : 337248301 ≤ 337379373) S160C12.total S160C13.total

theorem join_0_7 : (twinPrimeSegment 337379373 337641517).card = 885 := by
  simpa using combineTwinPrimeSegments (by decide : 337379373 ≤ 337510445)
    (by decide : 337510445 ≤ 337641517) S160C14.total S160C15.total

theorem join_1_0 : (twinPrimeSegment 335544365 336068653).card = 1794 := by
  simpa using combineTwinPrimeSegments (by decide : 335544365 ≤ 335806509)
    (by decide : 335806509 ≤ 336068653) join_0_0 join_0_1

theorem join_1_1 : (twinPrimeSegment 336068653 336592941).card = 1816 := by
  simpa using combineTwinPrimeSegments (by decide : 336068653 ≤ 336330797)
    (by decide : 336330797 ≤ 336592941) join_0_2 join_0_3

theorem join_1_2 : (twinPrimeSegment 336592941 337117229).card = 1804 := by
  simpa using combineTwinPrimeSegments (by decide : 336592941 ≤ 336855085)
    (by decide : 336855085 ≤ 337117229) join_0_4 join_0_5

theorem join_1_3 : (twinPrimeSegment 337117229 337641517).card = 1792 := by
  simpa using combineTwinPrimeSegments (by decide : 337117229 ≤ 337379373)
    (by decide : 337379373 ≤ 337641517) join_0_6 join_0_7

theorem join_2_0 : (twinPrimeSegment 335544365 336592941).card = 3610 := by
  simpa using combineTwinPrimeSegments (by decide : 335544365 ≤ 336068653)
    (by decide : 336068653 ≤ 336592941) join_1_0 join_1_1

theorem join_2_1 : (twinPrimeSegment 336592941 337641517).card = 3596 := by
  simpa using combineTwinPrimeSegments (by decide : 336592941 ≤ 337117229)
    (by decide : 337117229 ≤ 337641517) join_1_2 join_1_3

theorem join_3_0 : (twinPrimeSegment 335544365 337641517).card = 7206 := by
  simpa using combineTwinPrimeSegments (by decide : 335544365 ≤ 336592941)
    (by decide : 336592941 ≤ 337641517) join_2_0 join_2_1

theorem total : (twinPrimeSegment 335544365 337641517).card = 7206 := join_3_0

end S160All
end Sude.GeneratedTwinScan
