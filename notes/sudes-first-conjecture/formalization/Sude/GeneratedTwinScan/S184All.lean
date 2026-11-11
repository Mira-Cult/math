import Sude.GeneratedTwinScan.S184C00
import Sude.GeneratedTwinScan.S184C01
import Sude.GeneratedTwinScan.S184C02
import Sude.GeneratedTwinScan.S184C03
import Sude.GeneratedTwinScan.S184C04
import Sude.GeneratedTwinScan.S184C05
import Sude.GeneratedTwinScan.S184C06
import Sude.GeneratedTwinScan.S184C07
import Sude.GeneratedTwinScan.S184C08
import Sude.GeneratedTwinScan.S184C09
import Sude.GeneratedTwinScan.S184C10
import Sude.GeneratedTwinScan.S184C11
import Sude.GeneratedTwinScan.S184C12
import Sude.GeneratedTwinScan.S184C13
import Sude.GeneratedTwinScan.S184C14
import Sude.GeneratedTwinScan.S184C15

/-! Combined FT source segment; Lean kernel check required. -/
namespace Sude.GeneratedTwinScan
namespace S184All

theorem join_0_0 : (twinPrimeSegment 385876013 386138157).card = 862 := by
  simpa using combineTwinPrimeSegments (by decide : 385876013 ≤ 386007085)
    (by decide : 386007085 ≤ 386138157) S184C00.total S184C01.total

theorem join_0_1 : (twinPrimeSegment 386138157 386400301).card = 881 := by
  simpa using combineTwinPrimeSegments (by decide : 386138157 ≤ 386269229)
    (by decide : 386269229 ≤ 386400301) S184C02.total S184C03.total

theorem join_0_2 : (twinPrimeSegment 386400301 386662445).card = 884 := by
  simpa using combineTwinPrimeSegments (by decide : 386400301 ≤ 386531373)
    (by decide : 386531373 ≤ 386662445) S184C04.total S184C05.total

theorem join_0_3 : (twinPrimeSegment 386662445 386924589).card = 852 := by
  simpa using combineTwinPrimeSegments (by decide : 386662445 ≤ 386793517)
    (by decide : 386793517 ≤ 386924589) S184C06.total S184C07.total

theorem join_0_4 : (twinPrimeSegment 386924589 387186733).card = 914 := by
  simpa using combineTwinPrimeSegments (by decide : 386924589 ≤ 387055661)
    (by decide : 387055661 ≤ 387186733) S184C08.total S184C09.total

theorem join_0_5 : (twinPrimeSegment 387186733 387448877).card = 911 := by
  simpa using combineTwinPrimeSegments (by decide : 387186733 ≤ 387317805)
    (by decide : 387317805 ≤ 387448877) S184C10.total S184C11.total

theorem join_0_6 : (twinPrimeSegment 387448877 387711021).card = 886 := by
  simpa using combineTwinPrimeSegments (by decide : 387448877 ≤ 387579949)
    (by decide : 387579949 ≤ 387711021) S184C12.total S184C13.total

theorem join_0_7 : (twinPrimeSegment 387711021 387973165).card = 899 := by
  simpa using combineTwinPrimeSegments (by decide : 387711021 ≤ 387842093)
    (by decide : 387842093 ≤ 387973165) S184C14.total S184C15.total

theorem join_1_0 : (twinPrimeSegment 385876013 386400301).card = 1743 := by
  simpa using combineTwinPrimeSegments (by decide : 385876013 ≤ 386138157)
    (by decide : 386138157 ≤ 386400301) join_0_0 join_0_1

theorem join_1_1 : (twinPrimeSegment 386400301 386924589).card = 1736 := by
  simpa using combineTwinPrimeSegments (by decide : 386400301 ≤ 386662445)
    (by decide : 386662445 ≤ 386924589) join_0_2 join_0_3

theorem join_1_2 : (twinPrimeSegment 386924589 387448877).card = 1825 := by
  simpa using combineTwinPrimeSegments (by decide : 386924589 ≤ 387186733)
    (by decide : 387186733 ≤ 387448877) join_0_4 join_0_5

theorem join_1_3 : (twinPrimeSegment 387448877 387973165).card = 1785 := by
  simpa using combineTwinPrimeSegments (by decide : 387448877 ≤ 387711021)
    (by decide : 387711021 ≤ 387973165) join_0_6 join_0_7

theorem join_2_0 : (twinPrimeSegment 385876013 386924589).card = 3479 := by
  simpa using combineTwinPrimeSegments (by decide : 385876013 ≤ 386400301)
    (by decide : 386400301 ≤ 386924589) join_1_0 join_1_1

theorem join_2_1 : (twinPrimeSegment 386924589 387973165).card = 3610 := by
  simpa using combineTwinPrimeSegments (by decide : 386924589 ≤ 387448877)
    (by decide : 387448877 ≤ 387973165) join_1_2 join_1_3

theorem join_3_0 : (twinPrimeSegment 385876013 387973165).card = 7089 := by
  simpa using combineTwinPrimeSegments (by decide : 385876013 ≤ 386924589)
    (by decide : 386924589 ≤ 387973165) join_2_0 join_2_1

theorem total : (twinPrimeSegment 385876013 387973165).card = 7089 := join_3_0

end S184All
end Sude.GeneratedTwinScan
