import Sude.GeneratedTwinScan.S231C00
import Sude.GeneratedTwinScan.S231C01
import Sude.GeneratedTwinScan.S231C02
import Sude.GeneratedTwinScan.S231C03
import Sude.GeneratedTwinScan.S231C04
import Sude.GeneratedTwinScan.S231C05
import Sude.GeneratedTwinScan.S231C06
import Sude.GeneratedTwinScan.S231C07
import Sude.GeneratedTwinScan.S231C08
import Sude.GeneratedTwinScan.S231C09
import Sude.GeneratedTwinScan.S231C10
import Sude.GeneratedTwinScan.S231C11
import Sude.GeneratedTwinScan.S231C12
import Sude.GeneratedTwinScan.S231C13
import Sude.GeneratedTwinScan.S231C14
import Sude.GeneratedTwinScan.S231C15

/-! Combined FT source segment; Lean kernel check required. -/
namespace Sude.GeneratedTwinScan
namespace S231All

theorem join_0_0 : (twinPrimeSegment 484442157 484704301).card = 817 := by
  simpa using combineTwinPrimeSegments (by decide : 484442157 ≤ 484573229)
    (by decide : 484573229 ≤ 484704301) S231C00.total S231C01.total

theorem join_0_1 : (twinPrimeSegment 484704301 484966445).card = 866 := by
  simpa using combineTwinPrimeSegments (by decide : 484704301 ≤ 484835373)
    (by decide : 484835373 ≤ 484966445) S231C02.total S231C03.total

theorem join_0_2 : (twinPrimeSegment 484966445 485228589).card = 822 := by
  simpa using combineTwinPrimeSegments (by decide : 484966445 ≤ 485097517)
    (by decide : 485097517 ≤ 485228589) S231C04.total S231C05.total

theorem join_0_3 : (twinPrimeSegment 485228589 485490733).card = 849 := by
  simpa using combineTwinPrimeSegments (by decide : 485228589 ≤ 485359661)
    (by decide : 485359661 ≤ 485490733) S231C06.total S231C07.total

theorem join_0_4 : (twinPrimeSegment 485490733 485752877).card = 857 := by
  simpa using combineTwinPrimeSegments (by decide : 485490733 ≤ 485621805)
    (by decide : 485621805 ≤ 485752877) S231C08.total S231C09.total

theorem join_0_5 : (twinPrimeSegment 485752877 486015021).card = 872 := by
  simpa using combineTwinPrimeSegments (by decide : 485752877 ≤ 485883949)
    (by decide : 485883949 ≤ 486015021) S231C10.total S231C11.total

theorem join_0_6 : (twinPrimeSegment 486015021 486277165).card = 870 := by
  simpa using combineTwinPrimeSegments (by decide : 486015021 ≤ 486146093)
    (by decide : 486146093 ≤ 486277165) S231C12.total S231C13.total

theorem join_0_7 : (twinPrimeSegment 486277165 486539309).card = 898 := by
  simpa using combineTwinPrimeSegments (by decide : 486277165 ≤ 486408237)
    (by decide : 486408237 ≤ 486539309) S231C14.total S231C15.total

theorem join_1_0 : (twinPrimeSegment 484442157 484966445).card = 1683 := by
  simpa using combineTwinPrimeSegments (by decide : 484442157 ≤ 484704301)
    (by decide : 484704301 ≤ 484966445) join_0_0 join_0_1

theorem join_1_1 : (twinPrimeSegment 484966445 485490733).card = 1671 := by
  simpa using combineTwinPrimeSegments (by decide : 484966445 ≤ 485228589)
    (by decide : 485228589 ≤ 485490733) join_0_2 join_0_3

theorem join_1_2 : (twinPrimeSegment 485490733 486015021).card = 1729 := by
  simpa using combineTwinPrimeSegments (by decide : 485490733 ≤ 485752877)
    (by decide : 485752877 ≤ 486015021) join_0_4 join_0_5

theorem join_1_3 : (twinPrimeSegment 486015021 486539309).card = 1768 := by
  simpa using combineTwinPrimeSegments (by decide : 486015021 ≤ 486277165)
    (by decide : 486277165 ≤ 486539309) join_0_6 join_0_7

theorem join_2_0 : (twinPrimeSegment 484442157 485490733).card = 3354 := by
  simpa using combineTwinPrimeSegments (by decide : 484442157 ≤ 484966445)
    (by decide : 484966445 ≤ 485490733) join_1_0 join_1_1

theorem join_2_1 : (twinPrimeSegment 485490733 486539309).card = 3497 := by
  simpa using combineTwinPrimeSegments (by decide : 485490733 ≤ 486015021)
    (by decide : 486015021 ≤ 486539309) join_1_2 join_1_3

theorem join_3_0 : (twinPrimeSegment 484442157 486539309).card = 6851 := by
  simpa using combineTwinPrimeSegments (by decide : 484442157 ≤ 485490733)
    (by decide : 485490733 ≤ 486539309) join_2_0 join_2_1

theorem total : (twinPrimeSegment 484442157 486539309).card = 6851 := join_3_0

end S231All
end Sude.GeneratedTwinScan
