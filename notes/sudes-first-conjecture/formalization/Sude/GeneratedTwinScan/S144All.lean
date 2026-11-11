import Sude.GeneratedTwinScan.S144C00
import Sude.GeneratedTwinScan.S144C01
import Sude.GeneratedTwinScan.S144C02
import Sude.GeneratedTwinScan.S144C03
import Sude.GeneratedTwinScan.S144C04
import Sude.GeneratedTwinScan.S144C05
import Sude.GeneratedTwinScan.S144C06
import Sude.GeneratedTwinScan.S144C07
import Sude.GeneratedTwinScan.S144C08
import Sude.GeneratedTwinScan.S144C09
import Sude.GeneratedTwinScan.S144C10
import Sude.GeneratedTwinScan.S144C11
import Sude.GeneratedTwinScan.S144C12
import Sude.GeneratedTwinScan.S144C13
import Sude.GeneratedTwinScan.S144C14
import Sude.GeneratedTwinScan.S144C15

/-! Combined FT source segment; Lean kernel check required. -/
namespace Sude.GeneratedTwinScan
namespace S144All

theorem join_0_0 : (twinPrimeSegment 301989933 302252077).card = 958 := by
  simpa using combineTwinPrimeSegments (by decide : 301989933 ≤ 302121005)
    (by decide : 302121005 ≤ 302252077) S144C00.total S144C01.total

theorem join_0_1 : (twinPrimeSegment 302252077 302514221).card = 880 := by
  simpa using combineTwinPrimeSegments (by decide : 302252077 ≤ 302383149)
    (by decide : 302383149 ≤ 302514221) S144C02.total S144C03.total

theorem join_0_2 : (twinPrimeSegment 302514221 302776365).card = 903 := by
  simpa using combineTwinPrimeSegments (by decide : 302514221 ≤ 302645293)
    (by decide : 302645293 ≤ 302776365) S144C04.total S144C05.total

theorem join_0_3 : (twinPrimeSegment 302776365 303038509).card = 893 := by
  simpa using combineTwinPrimeSegments (by decide : 302776365 ≤ 302907437)
    (by decide : 302907437 ≤ 303038509) S144C06.total S144C07.total

theorem join_0_4 : (twinPrimeSegment 303038509 303300653).card = 919 := by
  simpa using combineTwinPrimeSegments (by decide : 303038509 ≤ 303169581)
    (by decide : 303169581 ≤ 303300653) S144C08.total S144C09.total

theorem join_0_5 : (twinPrimeSegment 303300653 303562797).card = 904 := by
  simpa using combineTwinPrimeSegments (by decide : 303300653 ≤ 303431725)
    (by decide : 303431725 ≤ 303562797) S144C10.total S144C11.total

theorem join_0_6 : (twinPrimeSegment 303562797 303824941).card = 825 := by
  simpa using combineTwinPrimeSegments (by decide : 303562797 ≤ 303693869)
    (by decide : 303693869 ≤ 303824941) S144C12.total S144C13.total

theorem join_0_7 : (twinPrimeSegment 303824941 304087085).card = 921 := by
  simpa using combineTwinPrimeSegments (by decide : 303824941 ≤ 303956013)
    (by decide : 303956013 ≤ 304087085) S144C14.total S144C15.total

theorem join_1_0 : (twinPrimeSegment 301989933 302514221).card = 1838 := by
  simpa using combineTwinPrimeSegments (by decide : 301989933 ≤ 302252077)
    (by decide : 302252077 ≤ 302514221) join_0_0 join_0_1

theorem join_1_1 : (twinPrimeSegment 302514221 303038509).card = 1796 := by
  simpa using combineTwinPrimeSegments (by decide : 302514221 ≤ 302776365)
    (by decide : 302776365 ≤ 303038509) join_0_2 join_0_3

theorem join_1_2 : (twinPrimeSegment 303038509 303562797).card = 1823 := by
  simpa using combineTwinPrimeSegments (by decide : 303038509 ≤ 303300653)
    (by decide : 303300653 ≤ 303562797) join_0_4 join_0_5

theorem join_1_3 : (twinPrimeSegment 303562797 304087085).card = 1746 := by
  simpa using combineTwinPrimeSegments (by decide : 303562797 ≤ 303824941)
    (by decide : 303824941 ≤ 304087085) join_0_6 join_0_7

theorem join_2_0 : (twinPrimeSegment 301989933 303038509).card = 3634 := by
  simpa using combineTwinPrimeSegments (by decide : 301989933 ≤ 302514221)
    (by decide : 302514221 ≤ 303038509) join_1_0 join_1_1

theorem join_2_1 : (twinPrimeSegment 303038509 304087085).card = 3569 := by
  simpa using combineTwinPrimeSegments (by decide : 303038509 ≤ 303562797)
    (by decide : 303562797 ≤ 304087085) join_1_2 join_1_3

theorem join_3_0 : (twinPrimeSegment 301989933 304087085).card = 7203 := by
  simpa using combineTwinPrimeSegments (by decide : 301989933 ≤ 303038509)
    (by decide : 303038509 ≤ 304087085) join_2_0 join_2_1

theorem total : (twinPrimeSegment 301989933 304087085).card = 7203 := join_3_0

end S144All
end Sude.GeneratedTwinScan
