import Sude.GeneratedTwinScan.S113C00
import Sude.GeneratedTwinScan.S113C01
import Sude.GeneratedTwinScan.S113C02
import Sude.GeneratedTwinScan.S113C03
import Sude.GeneratedTwinScan.S113C04
import Sude.GeneratedTwinScan.S113C05
import Sude.GeneratedTwinScan.S113C06
import Sude.GeneratedTwinScan.S113C07
import Sude.GeneratedTwinScan.S113C08
import Sude.GeneratedTwinScan.S113C09
import Sude.GeneratedTwinScan.S113C10
import Sude.GeneratedTwinScan.S113C11
import Sude.GeneratedTwinScan.S113C12
import Sude.GeneratedTwinScan.S113C13
import Sude.GeneratedTwinScan.S113C14
import Sude.GeneratedTwinScan.S113C15

/-! Combined FT source segment; Lean kernel check required. -/
namespace Sude.GeneratedTwinScan
namespace S113All

theorem join_0_0 : (twinPrimeSegment 236978221 237240365).card = 997 := by
  simpa using combineTwinPrimeSegments (by decide : 236978221 ≤ 237109293)
    (by decide : 237109293 ≤ 237240365) S113C00.total S113C01.total

theorem join_0_1 : (twinPrimeSegment 237240365 237502509).card = 915 := by
  simpa using combineTwinPrimeSegments (by decide : 237240365 ≤ 237371437)
    (by decide : 237371437 ≤ 237502509) S113C02.total S113C03.total

theorem join_0_2 : (twinPrimeSegment 237502509 237764653).card = 946 := by
  simpa using combineTwinPrimeSegments (by decide : 237502509 ≤ 237633581)
    (by decide : 237633581 ≤ 237764653) S113C04.total S113C05.total

theorem join_0_3 : (twinPrimeSegment 237764653 238026797).card = 976 := by
  simpa using combineTwinPrimeSegments (by decide : 237764653 ≤ 237895725)
    (by decide : 237895725 ≤ 238026797) S113C06.total S113C07.total

theorem join_0_4 : (twinPrimeSegment 238026797 238288941).card = 986 := by
  simpa using combineTwinPrimeSegments (by decide : 238026797 ≤ 238157869)
    (by decide : 238157869 ≤ 238288941) S113C08.total S113C09.total

theorem join_0_5 : (twinPrimeSegment 238288941 238551085).card = 881 := by
  simpa using combineTwinPrimeSegments (by decide : 238288941 ≤ 238420013)
    (by decide : 238420013 ≤ 238551085) S113C10.total S113C11.total

theorem join_0_6 : (twinPrimeSegment 238551085 238813229).card = 901 := by
  simpa using combineTwinPrimeSegments (by decide : 238551085 ≤ 238682157)
    (by decide : 238682157 ≤ 238813229) S113C12.total S113C13.total

theorem join_0_7 : (twinPrimeSegment 238813229 239075373).card = 918 := by
  simpa using combineTwinPrimeSegments (by decide : 238813229 ≤ 238944301)
    (by decide : 238944301 ≤ 239075373) S113C14.total S113C15.total

theorem join_1_0 : (twinPrimeSegment 236978221 237502509).card = 1912 := by
  simpa using combineTwinPrimeSegments (by decide : 236978221 ≤ 237240365)
    (by decide : 237240365 ≤ 237502509) join_0_0 join_0_1

theorem join_1_1 : (twinPrimeSegment 237502509 238026797).card = 1922 := by
  simpa using combineTwinPrimeSegments (by decide : 237502509 ≤ 237764653)
    (by decide : 237764653 ≤ 238026797) join_0_2 join_0_3

theorem join_1_2 : (twinPrimeSegment 238026797 238551085).card = 1867 := by
  simpa using combineTwinPrimeSegments (by decide : 238026797 ≤ 238288941)
    (by decide : 238288941 ≤ 238551085) join_0_4 join_0_5

theorem join_1_3 : (twinPrimeSegment 238551085 239075373).card = 1819 := by
  simpa using combineTwinPrimeSegments (by decide : 238551085 ≤ 238813229)
    (by decide : 238813229 ≤ 239075373) join_0_6 join_0_7

theorem join_2_0 : (twinPrimeSegment 236978221 238026797).card = 3834 := by
  simpa using combineTwinPrimeSegments (by decide : 236978221 ≤ 237502509)
    (by decide : 237502509 ≤ 238026797) join_1_0 join_1_1

theorem join_2_1 : (twinPrimeSegment 238026797 239075373).card = 3686 := by
  simpa using combineTwinPrimeSegments (by decide : 238026797 ≤ 238551085)
    (by decide : 238551085 ≤ 239075373) join_1_2 join_1_3

theorem join_3_0 : (twinPrimeSegment 236978221 239075373).card = 7520 := by
  simpa using combineTwinPrimeSegments (by decide : 236978221 ≤ 238026797)
    (by decide : 238026797 ≤ 239075373) join_2_0 join_2_1

theorem total : (twinPrimeSegment 236978221 239075373).card = 7520 := join_3_0

end S113All
end Sude.GeneratedTwinScan
