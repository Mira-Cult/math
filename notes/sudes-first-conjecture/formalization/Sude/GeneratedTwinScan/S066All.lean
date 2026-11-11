import Sude.GeneratedTwinScan.S066C00
import Sude.GeneratedTwinScan.S066C01
import Sude.GeneratedTwinScan.S066C02
import Sude.GeneratedTwinScan.S066C03
import Sude.GeneratedTwinScan.S066C04
import Sude.GeneratedTwinScan.S066C05
import Sude.GeneratedTwinScan.S066C06
import Sude.GeneratedTwinScan.S066C07
import Sude.GeneratedTwinScan.S066C08
import Sude.GeneratedTwinScan.S066C09
import Sude.GeneratedTwinScan.S066C10
import Sude.GeneratedTwinScan.S066C11
import Sude.GeneratedTwinScan.S066C12
import Sude.GeneratedTwinScan.S066C13
import Sude.GeneratedTwinScan.S066C14
import Sude.GeneratedTwinScan.S066C15

/-! Combined FT source segment; Lean kernel check required. -/
namespace Sude.GeneratedTwinScan
namespace S066All

theorem join_0_0 : (twinPrimeSegment 138412077 138674221).card = 991 := by
  simpa using combineTwinPrimeSegments (by decide : 138412077 ≤ 138543149)
    (by decide : 138543149 ≤ 138674221) S066C00.total S066C01.total

theorem join_0_1 : (twinPrimeSegment 138674221 138936365).card = 977 := by
  simpa using combineTwinPrimeSegments (by decide : 138674221 ≤ 138805293)
    (by decide : 138805293 ≤ 138936365) S066C02.total S066C03.total

theorem join_0_2 : (twinPrimeSegment 138936365 139198509).card = 1020 := by
  simpa using combineTwinPrimeSegments (by decide : 138936365 ≤ 139067437)
    (by decide : 139067437 ≤ 139198509) S066C04.total S066C05.total

theorem join_0_3 : (twinPrimeSegment 139198509 139460653).card = 1005 := by
  simpa using combineTwinPrimeSegments (by decide : 139198509 ≤ 139329581)
    (by decide : 139329581 ≤ 139460653) S066C06.total S066C07.total

theorem join_0_4 : (twinPrimeSegment 139460653 139722797).card = 1005 := by
  simpa using combineTwinPrimeSegments (by decide : 139460653 ≤ 139591725)
    (by decide : 139591725 ≤ 139722797) S066C08.total S066C09.total

theorem join_0_5 : (twinPrimeSegment 139722797 139984941).card = 970 := by
  simpa using combineTwinPrimeSegments (by decide : 139722797 ≤ 139853869)
    (by decide : 139853869 ≤ 139984941) S066C10.total S066C11.total

theorem join_0_6 : (twinPrimeSegment 139984941 140247085).card = 961 := by
  simpa using combineTwinPrimeSegments (by decide : 139984941 ≤ 140116013)
    (by decide : 140116013 ≤ 140247085) S066C12.total S066C13.total

theorem join_0_7 : (twinPrimeSegment 140247085 140509229).card = 966 := by
  simpa using combineTwinPrimeSegments (by decide : 140247085 ≤ 140378157)
    (by decide : 140378157 ≤ 140509229) S066C14.total S066C15.total

theorem join_1_0 : (twinPrimeSegment 138412077 138936365).card = 1968 := by
  simpa using combineTwinPrimeSegments (by decide : 138412077 ≤ 138674221)
    (by decide : 138674221 ≤ 138936365) join_0_0 join_0_1

theorem join_1_1 : (twinPrimeSegment 138936365 139460653).card = 2025 := by
  simpa using combineTwinPrimeSegments (by decide : 138936365 ≤ 139198509)
    (by decide : 139198509 ≤ 139460653) join_0_2 join_0_3

theorem join_1_2 : (twinPrimeSegment 139460653 139984941).card = 1975 := by
  simpa using combineTwinPrimeSegments (by decide : 139460653 ≤ 139722797)
    (by decide : 139722797 ≤ 139984941) join_0_4 join_0_5

theorem join_1_3 : (twinPrimeSegment 139984941 140509229).card = 1927 := by
  simpa using combineTwinPrimeSegments (by decide : 139984941 ≤ 140247085)
    (by decide : 140247085 ≤ 140509229) join_0_6 join_0_7

theorem join_2_0 : (twinPrimeSegment 138412077 139460653).card = 3993 := by
  simpa using combineTwinPrimeSegments (by decide : 138412077 ≤ 138936365)
    (by decide : 138936365 ≤ 139460653) join_1_0 join_1_1

theorem join_2_1 : (twinPrimeSegment 139460653 140509229).card = 3902 := by
  simpa using combineTwinPrimeSegments (by decide : 139460653 ≤ 139984941)
    (by decide : 139984941 ≤ 140509229) join_1_2 join_1_3

theorem join_3_0 : (twinPrimeSegment 138412077 140509229).card = 7895 := by
  simpa using combineTwinPrimeSegments (by decide : 138412077 ≤ 139460653)
    (by decide : 139460653 ≤ 140509229) join_2_0 join_2_1

theorem total : (twinPrimeSegment 138412077 140509229).card = 7895 := join_3_0

end S066All
end Sude.GeneratedTwinScan
