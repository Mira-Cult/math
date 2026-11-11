import Sude.GeneratedTwinScan.S043C00
import Sude.GeneratedTwinScan.S043C01
import Sude.GeneratedTwinScan.S043C02
import Sude.GeneratedTwinScan.S043C03
import Sude.GeneratedTwinScan.S043C04
import Sude.GeneratedTwinScan.S043C05
import Sude.GeneratedTwinScan.S043C06
import Sude.GeneratedTwinScan.S043C07
import Sude.GeneratedTwinScan.S043C08
import Sude.GeneratedTwinScan.S043C09
import Sude.GeneratedTwinScan.S043C10
import Sude.GeneratedTwinScan.S043C11
import Sude.GeneratedTwinScan.S043C12
import Sude.GeneratedTwinScan.S043C13
import Sude.GeneratedTwinScan.S043C14
import Sude.GeneratedTwinScan.S043C15

/-! Combined FT source segment; Lean kernel check required. -/
namespace Sude.GeneratedTwinScan
namespace S043All

theorem join_0_0 : (twinPrimeSegment 90177581 90439725).card = 1048 := by
  simpa using combineTwinPrimeSegments (by decide : 90177581 ≤ 90308653)
    (by decide : 90308653 ≤ 90439725) S043C00.total S043C01.total

theorem join_0_1 : (twinPrimeSegment 90439725 90701869).card = 1056 := by
  simpa using combineTwinPrimeSegments (by decide : 90439725 ≤ 90570797)
    (by decide : 90570797 ≤ 90701869) S043C02.total S043C03.total

theorem join_0_2 : (twinPrimeSegment 90701869 90964013).card = 1012 := by
  simpa using combineTwinPrimeSegments (by decide : 90701869 ≤ 90832941)
    (by decide : 90832941 ≤ 90964013) S043C04.total S043C05.total

theorem join_0_3 : (twinPrimeSegment 90964013 91226157).card = 1055 := by
  simpa using combineTwinPrimeSegments (by decide : 90964013 ≤ 91095085)
    (by decide : 91095085 ≤ 91226157) S043C06.total S043C07.total

theorem join_0_4 : (twinPrimeSegment 91226157 91488301).card = 1038 := by
  simpa using combineTwinPrimeSegments (by decide : 91226157 ≤ 91357229)
    (by decide : 91357229 ≤ 91488301) S043C08.total S043C09.total

theorem join_0_5 : (twinPrimeSegment 91488301 91750445).card = 1016 := by
  simpa using combineTwinPrimeSegments (by decide : 91488301 ≤ 91619373)
    (by decide : 91619373 ≤ 91750445) S043C10.total S043C11.total

theorem join_0_6 : (twinPrimeSegment 91750445 92012589).card = 1026 := by
  simpa using combineTwinPrimeSegments (by decide : 91750445 ≤ 91881517)
    (by decide : 91881517 ≤ 92012589) S043C12.total S043C13.total

theorem join_0_7 : (twinPrimeSegment 92012589 92274733).card = 1074 := by
  simpa using combineTwinPrimeSegments (by decide : 92012589 ≤ 92143661)
    (by decide : 92143661 ≤ 92274733) S043C14.total S043C15.total

theorem join_1_0 : (twinPrimeSegment 90177581 90701869).card = 2104 := by
  simpa using combineTwinPrimeSegments (by decide : 90177581 ≤ 90439725)
    (by decide : 90439725 ≤ 90701869) join_0_0 join_0_1

theorem join_1_1 : (twinPrimeSegment 90701869 91226157).card = 2067 := by
  simpa using combineTwinPrimeSegments (by decide : 90701869 ≤ 90964013)
    (by decide : 90964013 ≤ 91226157) join_0_2 join_0_3

theorem join_1_2 : (twinPrimeSegment 91226157 91750445).card = 2054 := by
  simpa using combineTwinPrimeSegments (by decide : 91226157 ≤ 91488301)
    (by decide : 91488301 ≤ 91750445) join_0_4 join_0_5

theorem join_1_3 : (twinPrimeSegment 91750445 92274733).card = 2100 := by
  simpa using combineTwinPrimeSegments (by decide : 91750445 ≤ 92012589)
    (by decide : 92012589 ≤ 92274733) join_0_6 join_0_7

theorem join_2_0 : (twinPrimeSegment 90177581 91226157).card = 4171 := by
  simpa using combineTwinPrimeSegments (by decide : 90177581 ≤ 90701869)
    (by decide : 90701869 ≤ 91226157) join_1_0 join_1_1

theorem join_2_1 : (twinPrimeSegment 91226157 92274733).card = 4154 := by
  simpa using combineTwinPrimeSegments (by decide : 91226157 ≤ 91750445)
    (by decide : 91750445 ≤ 92274733) join_1_2 join_1_3

theorem join_3_0 : (twinPrimeSegment 90177581 92274733).card = 8325 := by
  simpa using combineTwinPrimeSegments (by decide : 90177581 ≤ 91226157)
    (by decide : 91226157 ≤ 92274733) join_2_0 join_2_1

theorem total : (twinPrimeSegment 90177581 92274733).card = 8325 := join_3_0

end S043All
end Sude.GeneratedTwinScan
