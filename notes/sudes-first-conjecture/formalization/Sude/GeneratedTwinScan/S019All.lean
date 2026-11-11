import Sude.GeneratedTwinScan.S019C00
import Sude.GeneratedTwinScan.S019C01
import Sude.GeneratedTwinScan.S019C02
import Sude.GeneratedTwinScan.S019C03
import Sude.GeneratedTwinScan.S019C04
import Sude.GeneratedTwinScan.S019C05
import Sude.GeneratedTwinScan.S019C06
import Sude.GeneratedTwinScan.S019C07
import Sude.GeneratedTwinScan.S019C08
import Sude.GeneratedTwinScan.S019C09
import Sude.GeneratedTwinScan.S019C10
import Sude.GeneratedTwinScan.S019C11
import Sude.GeneratedTwinScan.S019C12
import Sude.GeneratedTwinScan.S019C13
import Sude.GeneratedTwinScan.S019C14
import Sude.GeneratedTwinScan.S019C15

/-! Combined FT source segment; Lean kernel check required. -/
namespace Sude.GeneratedTwinScan
namespace S019All

theorem join_0_0 : (twinPrimeSegment 39845933 40108077).card = 1128 := by
  simpa using combineTwinPrimeSegments (by decide : 39845933 ≤ 39977005)
    (by decide : 39977005 ≤ 40108077) S019C00.total S019C01.total

theorem join_0_1 : (twinPrimeSegment 40108077 40370221).card = 1134 := by
  simpa using combineTwinPrimeSegments (by decide : 40108077 ≤ 40239149)
    (by decide : 40239149 ≤ 40370221) S019C02.total S019C03.total

theorem join_0_2 : (twinPrimeSegment 40370221 40632365).card = 1086 := by
  simpa using combineTwinPrimeSegments (by decide : 40370221 ≤ 40501293)
    (by decide : 40501293 ≤ 40632365) S019C04.total S019C05.total

theorem join_0_3 : (twinPrimeSegment 40632365 40894509).card = 1171 := by
  simpa using combineTwinPrimeSegments (by decide : 40632365 ≤ 40763437)
    (by decide : 40763437 ≤ 40894509) S019C06.total S019C07.total

theorem join_0_4 : (twinPrimeSegment 40894509 41156653).card = 1100 := by
  simpa using combineTwinPrimeSegments (by decide : 40894509 ≤ 41025581)
    (by decide : 41025581 ≤ 41156653) S019C08.total S019C09.total

theorem join_0_5 : (twinPrimeSegment 41156653 41418797).card = 1086 := by
  simpa using combineTwinPrimeSegments (by decide : 41156653 ≤ 41287725)
    (by decide : 41287725 ≤ 41418797) S019C10.total S019C11.total

theorem join_0_6 : (twinPrimeSegment 41418797 41680941).card = 1092 := by
  simpa using combineTwinPrimeSegments (by decide : 41418797 ≤ 41549869)
    (by decide : 41549869 ≤ 41680941) S019C12.total S019C13.total

theorem join_0_7 : (twinPrimeSegment 41680941 41943085).card = 1115 := by
  simpa using combineTwinPrimeSegments (by decide : 41680941 ≤ 41812013)
    (by decide : 41812013 ≤ 41943085) S019C14.total S019C15.total

theorem join_1_0 : (twinPrimeSegment 39845933 40370221).card = 2262 := by
  simpa using combineTwinPrimeSegments (by decide : 39845933 ≤ 40108077)
    (by decide : 40108077 ≤ 40370221) join_0_0 join_0_1

theorem join_1_1 : (twinPrimeSegment 40370221 40894509).card = 2257 := by
  simpa using combineTwinPrimeSegments (by decide : 40370221 ≤ 40632365)
    (by decide : 40632365 ≤ 40894509) join_0_2 join_0_3

theorem join_1_2 : (twinPrimeSegment 40894509 41418797).card = 2186 := by
  simpa using combineTwinPrimeSegments (by decide : 40894509 ≤ 41156653)
    (by decide : 41156653 ≤ 41418797) join_0_4 join_0_5

theorem join_1_3 : (twinPrimeSegment 41418797 41943085).card = 2207 := by
  simpa using combineTwinPrimeSegments (by decide : 41418797 ≤ 41680941)
    (by decide : 41680941 ≤ 41943085) join_0_6 join_0_7

theorem join_2_0 : (twinPrimeSegment 39845933 40894509).card = 4519 := by
  simpa using combineTwinPrimeSegments (by decide : 39845933 ≤ 40370221)
    (by decide : 40370221 ≤ 40894509) join_1_0 join_1_1

theorem join_2_1 : (twinPrimeSegment 40894509 41943085).card = 4393 := by
  simpa using combineTwinPrimeSegments (by decide : 40894509 ≤ 41418797)
    (by decide : 41418797 ≤ 41943085) join_1_2 join_1_3

theorem join_3_0 : (twinPrimeSegment 39845933 41943085).card = 8912 := by
  simpa using combineTwinPrimeSegments (by decide : 39845933 ≤ 40894509)
    (by decide : 40894509 ≤ 41943085) join_2_0 join_2_1

theorem total : (twinPrimeSegment 39845933 41943085).card = 8912 := join_3_0

end S019All
end Sude.GeneratedTwinScan
