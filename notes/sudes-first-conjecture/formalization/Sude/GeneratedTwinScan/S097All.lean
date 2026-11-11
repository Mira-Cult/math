import Sude.GeneratedTwinScan.S097C00
import Sude.GeneratedTwinScan.S097C01
import Sude.GeneratedTwinScan.S097C02
import Sude.GeneratedTwinScan.S097C03
import Sude.GeneratedTwinScan.S097C04
import Sude.GeneratedTwinScan.S097C05
import Sude.GeneratedTwinScan.S097C06
import Sude.GeneratedTwinScan.S097C07
import Sude.GeneratedTwinScan.S097C08
import Sude.GeneratedTwinScan.S097C09
import Sude.GeneratedTwinScan.S097C10
import Sude.GeneratedTwinScan.S097C11
import Sude.GeneratedTwinScan.S097C12
import Sude.GeneratedTwinScan.S097C13
import Sude.GeneratedTwinScan.S097C14
import Sude.GeneratedTwinScan.S097C15

/-! Combined FT source segment; Lean kernel check required. -/
namespace Sude.GeneratedTwinScan
namespace S097All

theorem join_0_0 : (twinPrimeSegment 203423789 203685933).card = 954 := by
  simpa using combineTwinPrimeSegments (by decide : 203423789 ≤ 203554861)
    (by decide : 203554861 ≤ 203685933) S097C00.total S097C01.total

theorem join_0_1 : (twinPrimeSegment 203685933 203948077).card = 920 := by
  simpa using combineTwinPrimeSegments (by decide : 203685933 ≤ 203817005)
    (by decide : 203817005 ≤ 203948077) S097C02.total S097C03.total

theorem join_0_2 : (twinPrimeSegment 203948077 204210221).card = 945 := by
  simpa using combineTwinPrimeSegments (by decide : 203948077 ≤ 204079149)
    (by decide : 204079149 ≤ 204210221) S097C04.total S097C05.total

theorem join_0_3 : (twinPrimeSegment 204210221 204472365).card = 962 := by
  simpa using combineTwinPrimeSegments (by decide : 204210221 ≤ 204341293)
    (by decide : 204341293 ≤ 204472365) S097C06.total S097C07.total

theorem join_0_4 : (twinPrimeSegment 204472365 204734509).card = 975 := by
  simpa using combineTwinPrimeSegments (by decide : 204472365 ≤ 204603437)
    (by decide : 204603437 ≤ 204734509) S097C08.total S097C09.total

theorem join_0_5 : (twinPrimeSegment 204734509 204996653).card = 1002 := by
  simpa using combineTwinPrimeSegments (by decide : 204734509 ≤ 204865581)
    (by decide : 204865581 ≤ 204996653) S097C10.total S097C11.total

theorem join_0_6 : (twinPrimeSegment 204996653 205258797).card = 914 := by
  simpa using combineTwinPrimeSegments (by decide : 204996653 ≤ 205127725)
    (by decide : 205127725 ≤ 205258797) S097C12.total S097C13.total

theorem join_0_7 : (twinPrimeSegment 205258797 205520941).card = 894 := by
  simpa using combineTwinPrimeSegments (by decide : 205258797 ≤ 205389869)
    (by decide : 205389869 ≤ 205520941) S097C14.total S097C15.total

theorem join_1_0 : (twinPrimeSegment 203423789 203948077).card = 1874 := by
  simpa using combineTwinPrimeSegments (by decide : 203423789 ≤ 203685933)
    (by decide : 203685933 ≤ 203948077) join_0_0 join_0_1

theorem join_1_1 : (twinPrimeSegment 203948077 204472365).card = 1907 := by
  simpa using combineTwinPrimeSegments (by decide : 203948077 ≤ 204210221)
    (by decide : 204210221 ≤ 204472365) join_0_2 join_0_3

theorem join_1_2 : (twinPrimeSegment 204472365 204996653).card = 1977 := by
  simpa using combineTwinPrimeSegments (by decide : 204472365 ≤ 204734509)
    (by decide : 204734509 ≤ 204996653) join_0_4 join_0_5

theorem join_1_3 : (twinPrimeSegment 204996653 205520941).card = 1808 := by
  simpa using combineTwinPrimeSegments (by decide : 204996653 ≤ 205258797)
    (by decide : 205258797 ≤ 205520941) join_0_6 join_0_7

theorem join_2_0 : (twinPrimeSegment 203423789 204472365).card = 3781 := by
  simpa using combineTwinPrimeSegments (by decide : 203423789 ≤ 203948077)
    (by decide : 203948077 ≤ 204472365) join_1_0 join_1_1

theorem join_2_1 : (twinPrimeSegment 204472365 205520941).card = 3785 := by
  simpa using combineTwinPrimeSegments (by decide : 204472365 ≤ 204996653)
    (by decide : 204996653 ≤ 205520941) join_1_2 join_1_3

theorem join_3_0 : (twinPrimeSegment 203423789 205520941).card = 7566 := by
  simpa using combineTwinPrimeSegments (by decide : 203423789 ≤ 204472365)
    (by decide : 204472365 ≤ 205520941) join_2_0 join_2_1

theorem total : (twinPrimeSegment 203423789 205520941).card = 7566 := join_3_0

end S097All
end Sude.GeneratedTwinScan
