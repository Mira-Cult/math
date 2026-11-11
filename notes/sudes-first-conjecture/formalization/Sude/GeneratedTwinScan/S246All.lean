import Sude.GeneratedTwinScan.S246C00
import Sude.GeneratedTwinScan.S246C01
import Sude.GeneratedTwinScan.S246C02
import Sude.GeneratedTwinScan.S246C03
import Sude.GeneratedTwinScan.S246C04
import Sude.GeneratedTwinScan.S246C05
import Sude.GeneratedTwinScan.S246C06
import Sude.GeneratedTwinScan.S246C07
import Sude.GeneratedTwinScan.S246C08
import Sude.GeneratedTwinScan.S246C09
import Sude.GeneratedTwinScan.S246C10
import Sude.GeneratedTwinScan.S246C11
import Sude.GeneratedTwinScan.S246C12
import Sude.GeneratedTwinScan.S246C13
import Sude.GeneratedTwinScan.S246C14
import Sude.GeneratedTwinScan.S246C15

/-! Combined FT source segment; Lean kernel check required. -/
namespace Sude.GeneratedTwinScan
namespace S246All

theorem join_0_0 : (twinPrimeSegment 515899437 516161581).card = 877 := by
  simpa using combineTwinPrimeSegments (by decide : 515899437 ≤ 516030509)
    (by decide : 516030509 ≤ 516161581) S246C00.total S246C01.total

theorem join_0_1 : (twinPrimeSegment 516161581 516423725).card = 863 := by
  simpa using combineTwinPrimeSegments (by decide : 516161581 ≤ 516292653)
    (by decide : 516292653 ≤ 516423725) S246C02.total S246C03.total

theorem join_0_2 : (twinPrimeSegment 516423725 516685869).card = 910 := by
  simpa using combineTwinPrimeSegments (by decide : 516423725 ≤ 516554797)
    (by decide : 516554797 ≤ 516685869) S246C04.total S246C05.total

theorem join_0_3 : (twinPrimeSegment 516685869 516948013).card = 853 := by
  simpa using combineTwinPrimeSegments (by decide : 516685869 ≤ 516816941)
    (by decide : 516816941 ≤ 516948013) S246C06.total S246C07.total

theorem join_0_4 : (twinPrimeSegment 516948013 517210157).card = 820 := by
  simpa using combineTwinPrimeSegments (by decide : 516948013 ≤ 517079085)
    (by decide : 517079085 ≤ 517210157) S246C08.total S246C09.total

theorem join_0_5 : (twinPrimeSegment 517210157 517472301).card = 846 := by
  simpa using combineTwinPrimeSegments (by decide : 517210157 ≤ 517341229)
    (by decide : 517341229 ≤ 517472301) S246C10.total S246C11.total

theorem join_0_6 : (twinPrimeSegment 517472301 517734445).card = 811 := by
  simpa using combineTwinPrimeSegments (by decide : 517472301 ≤ 517603373)
    (by decide : 517603373 ≤ 517734445) S246C12.total S246C13.total

theorem join_0_7 : (twinPrimeSegment 517734445 517996589).card = 882 := by
  simpa using combineTwinPrimeSegments (by decide : 517734445 ≤ 517865517)
    (by decide : 517865517 ≤ 517996589) S246C14.total S246C15.total

theorem join_1_0 : (twinPrimeSegment 515899437 516423725).card = 1740 := by
  simpa using combineTwinPrimeSegments (by decide : 515899437 ≤ 516161581)
    (by decide : 516161581 ≤ 516423725) join_0_0 join_0_1

theorem join_1_1 : (twinPrimeSegment 516423725 516948013).card = 1763 := by
  simpa using combineTwinPrimeSegments (by decide : 516423725 ≤ 516685869)
    (by decide : 516685869 ≤ 516948013) join_0_2 join_0_3

theorem join_1_2 : (twinPrimeSegment 516948013 517472301).card = 1666 := by
  simpa using combineTwinPrimeSegments (by decide : 516948013 ≤ 517210157)
    (by decide : 517210157 ≤ 517472301) join_0_4 join_0_5

theorem join_1_3 : (twinPrimeSegment 517472301 517996589).card = 1693 := by
  simpa using combineTwinPrimeSegments (by decide : 517472301 ≤ 517734445)
    (by decide : 517734445 ≤ 517996589) join_0_6 join_0_7

theorem join_2_0 : (twinPrimeSegment 515899437 516948013).card = 3503 := by
  simpa using combineTwinPrimeSegments (by decide : 515899437 ≤ 516423725)
    (by decide : 516423725 ≤ 516948013) join_1_0 join_1_1

theorem join_2_1 : (twinPrimeSegment 516948013 517996589).card = 3359 := by
  simpa using combineTwinPrimeSegments (by decide : 516948013 ≤ 517472301)
    (by decide : 517472301 ≤ 517996589) join_1_2 join_1_3

theorem join_3_0 : (twinPrimeSegment 515899437 517996589).card = 6862 := by
  simpa using combineTwinPrimeSegments (by decide : 515899437 ≤ 516948013)
    (by decide : 516948013 ≤ 517996589) join_2_0 join_2_1

theorem total : (twinPrimeSegment 515899437 517996589).card = 6862 := join_3_0

end S246All
end Sude.GeneratedTwinScan
