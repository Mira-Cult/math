import Sude.GeneratedTwinScan.S207C00
import Sude.GeneratedTwinScan.S207C01
import Sude.GeneratedTwinScan.S207C02
import Sude.GeneratedTwinScan.S207C03
import Sude.GeneratedTwinScan.S207C04
import Sude.GeneratedTwinScan.S207C05
import Sude.GeneratedTwinScan.S207C06
import Sude.GeneratedTwinScan.S207C07
import Sude.GeneratedTwinScan.S207C08
import Sude.GeneratedTwinScan.S207C09
import Sude.GeneratedTwinScan.S207C10
import Sude.GeneratedTwinScan.S207C11
import Sude.GeneratedTwinScan.S207C12
import Sude.GeneratedTwinScan.S207C13
import Sude.GeneratedTwinScan.S207C14
import Sude.GeneratedTwinScan.S207C15

/-! Combined FT source segment; Lean kernel check required. -/
namespace Sude.GeneratedTwinScan
namespace S207All

theorem join_0_0 : (twinPrimeSegment 434110509 434372653).card = 920 := by
  simpa using combineTwinPrimeSegments (by decide : 434110509 ≤ 434241581)
    (by decide : 434241581 ≤ 434372653) S207C00.total S207C01.total

theorem join_0_1 : (twinPrimeSegment 434372653 434634797).card = 905 := by
  simpa using combineTwinPrimeSegments (by decide : 434372653 ≤ 434503725)
    (by decide : 434503725 ≤ 434634797) S207C02.total S207C03.total

theorem join_0_2 : (twinPrimeSegment 434634797 434896941).card = 877 := by
  simpa using combineTwinPrimeSegments (by decide : 434634797 ≤ 434765869)
    (by decide : 434765869 ≤ 434896941) S207C04.total S207C05.total

theorem join_0_3 : (twinPrimeSegment 434896941 435159085).card = 848 := by
  simpa using combineTwinPrimeSegments (by decide : 434896941 ≤ 435028013)
    (by decide : 435028013 ≤ 435159085) S207C06.total S207C07.total

theorem join_0_4 : (twinPrimeSegment 435159085 435421229).card = 877 := by
  simpa using combineTwinPrimeSegments (by decide : 435159085 ≤ 435290157)
    (by decide : 435290157 ≤ 435421229) S207C08.total S207C09.total

theorem join_0_5 : (twinPrimeSegment 435421229 435683373).card = 926 := by
  simpa using combineTwinPrimeSegments (by decide : 435421229 ≤ 435552301)
    (by decide : 435552301 ≤ 435683373) S207C10.total S207C11.total

theorem join_0_6 : (twinPrimeSegment 435683373 435945517).card = 883 := by
  simpa using combineTwinPrimeSegments (by decide : 435683373 ≤ 435814445)
    (by decide : 435814445 ≤ 435945517) S207C12.total S207C13.total

theorem join_0_7 : (twinPrimeSegment 435945517 436207661).card = 859 := by
  simpa using combineTwinPrimeSegments (by decide : 435945517 ≤ 436076589)
    (by decide : 436076589 ≤ 436207661) S207C14.total S207C15.total

theorem join_1_0 : (twinPrimeSegment 434110509 434634797).card = 1825 := by
  simpa using combineTwinPrimeSegments (by decide : 434110509 ≤ 434372653)
    (by decide : 434372653 ≤ 434634797) join_0_0 join_0_1

theorem join_1_1 : (twinPrimeSegment 434634797 435159085).card = 1725 := by
  simpa using combineTwinPrimeSegments (by decide : 434634797 ≤ 434896941)
    (by decide : 434896941 ≤ 435159085) join_0_2 join_0_3

theorem join_1_2 : (twinPrimeSegment 435159085 435683373).card = 1803 := by
  simpa using combineTwinPrimeSegments (by decide : 435159085 ≤ 435421229)
    (by decide : 435421229 ≤ 435683373) join_0_4 join_0_5

theorem join_1_3 : (twinPrimeSegment 435683373 436207661).card = 1742 := by
  simpa using combineTwinPrimeSegments (by decide : 435683373 ≤ 435945517)
    (by decide : 435945517 ≤ 436207661) join_0_6 join_0_7

theorem join_2_0 : (twinPrimeSegment 434110509 435159085).card = 3550 := by
  simpa using combineTwinPrimeSegments (by decide : 434110509 ≤ 434634797)
    (by decide : 434634797 ≤ 435159085) join_1_0 join_1_1

theorem join_2_1 : (twinPrimeSegment 435159085 436207661).card = 3545 := by
  simpa using combineTwinPrimeSegments (by decide : 435159085 ≤ 435683373)
    (by decide : 435683373 ≤ 436207661) join_1_2 join_1_3

theorem join_3_0 : (twinPrimeSegment 434110509 436207661).card = 7095 := by
  simpa using combineTwinPrimeSegments (by decide : 434110509 ≤ 435159085)
    (by decide : 435159085 ≤ 436207661) join_2_0 join_2_1

theorem total : (twinPrimeSegment 434110509 436207661).card = 7095 := join_3_0

end S207All
end Sude.GeneratedTwinScan
