import Sude.GeneratedTwinScan.S106C00
import Sude.GeneratedTwinScan.S106C01
import Sude.GeneratedTwinScan.S106C02
import Sude.GeneratedTwinScan.S106C03
import Sude.GeneratedTwinScan.S106C04
import Sude.GeneratedTwinScan.S106C05
import Sude.GeneratedTwinScan.S106C06
import Sude.GeneratedTwinScan.S106C07
import Sude.GeneratedTwinScan.S106C08
import Sude.GeneratedTwinScan.S106C09
import Sude.GeneratedTwinScan.S106C10
import Sude.GeneratedTwinScan.S106C11
import Sude.GeneratedTwinScan.S106C12
import Sude.GeneratedTwinScan.S106C13
import Sude.GeneratedTwinScan.S106C14
import Sude.GeneratedTwinScan.S106C15

/-! Combined FT source segment; Lean kernel check required. -/
namespace Sude.GeneratedTwinScan
namespace S106All

theorem join_0_0 : (twinPrimeSegment 222298157 222560301).card = 910 := by
  simpa using combineTwinPrimeSegments (by decide : 222298157 ≤ 222429229)
    (by decide : 222429229 ≤ 222560301) S106C00.total S106C01.total

theorem join_0_1 : (twinPrimeSegment 222560301 222822445).card = 934 := by
  simpa using combineTwinPrimeSegments (by decide : 222560301 ≤ 222691373)
    (by decide : 222691373 ≤ 222822445) S106C02.total S106C03.total

theorem join_0_2 : (twinPrimeSegment 222822445 223084589).card = 968 := by
  simpa using combineTwinPrimeSegments (by decide : 222822445 ≤ 222953517)
    (by decide : 222953517 ≤ 223084589) S106C04.total S106C05.total

theorem join_0_3 : (twinPrimeSegment 223084589 223346733).card = 949 := by
  simpa using combineTwinPrimeSegments (by decide : 223084589 ≤ 223215661)
    (by decide : 223215661 ≤ 223346733) S106C06.total S106C07.total

theorem join_0_4 : (twinPrimeSegment 223346733 223608877).card = 1004 := by
  simpa using combineTwinPrimeSegments (by decide : 223346733 ≤ 223477805)
    (by decide : 223477805 ≤ 223608877) S106C08.total S106C09.total

theorem join_0_5 : (twinPrimeSegment 223608877 223871021).card = 946 := by
  simpa using combineTwinPrimeSegments (by decide : 223608877 ≤ 223739949)
    (by decide : 223739949 ≤ 223871021) S106C10.total S106C11.total

theorem join_0_6 : (twinPrimeSegment 223871021 224133165).card = 964 := by
  simpa using combineTwinPrimeSegments (by decide : 223871021 ≤ 224002093)
    (by decide : 224002093 ≤ 224133165) S106C12.total S106C13.total

theorem join_0_7 : (twinPrimeSegment 224133165 224395309).card = 947 := by
  simpa using combineTwinPrimeSegments (by decide : 224133165 ≤ 224264237)
    (by decide : 224264237 ≤ 224395309) S106C14.total S106C15.total

theorem join_1_0 : (twinPrimeSegment 222298157 222822445).card = 1844 := by
  simpa using combineTwinPrimeSegments (by decide : 222298157 ≤ 222560301)
    (by decide : 222560301 ≤ 222822445) join_0_0 join_0_1

theorem join_1_1 : (twinPrimeSegment 222822445 223346733).card = 1917 := by
  simpa using combineTwinPrimeSegments (by decide : 222822445 ≤ 223084589)
    (by decide : 223084589 ≤ 223346733) join_0_2 join_0_3

theorem join_1_2 : (twinPrimeSegment 223346733 223871021).card = 1950 := by
  simpa using combineTwinPrimeSegments (by decide : 223346733 ≤ 223608877)
    (by decide : 223608877 ≤ 223871021) join_0_4 join_0_5

theorem join_1_3 : (twinPrimeSegment 223871021 224395309).card = 1911 := by
  simpa using combineTwinPrimeSegments (by decide : 223871021 ≤ 224133165)
    (by decide : 224133165 ≤ 224395309) join_0_6 join_0_7

theorem join_2_0 : (twinPrimeSegment 222298157 223346733).card = 3761 := by
  simpa using combineTwinPrimeSegments (by decide : 222298157 ≤ 222822445)
    (by decide : 222822445 ≤ 223346733) join_1_0 join_1_1

theorem join_2_1 : (twinPrimeSegment 223346733 224395309).card = 3861 := by
  simpa using combineTwinPrimeSegments (by decide : 223346733 ≤ 223871021)
    (by decide : 223871021 ≤ 224395309) join_1_2 join_1_3

theorem join_3_0 : (twinPrimeSegment 222298157 224395309).card = 7622 := by
  simpa using combineTwinPrimeSegments (by decide : 222298157 ≤ 223346733)
    (by decide : 223346733 ≤ 224395309) join_2_0 join_2_1

theorem total : (twinPrimeSegment 222298157 224395309).card = 7622 := join_3_0

end S106All
end Sude.GeneratedTwinScan
