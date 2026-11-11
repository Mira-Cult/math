import Sude.GeneratedTwinScan.S100C00
import Sude.GeneratedTwinScan.S100C01
import Sude.GeneratedTwinScan.S100C02
import Sude.GeneratedTwinScan.S100C03
import Sude.GeneratedTwinScan.S100C04
import Sude.GeneratedTwinScan.S100C05
import Sude.GeneratedTwinScan.S100C06
import Sude.GeneratedTwinScan.S100C07
import Sude.GeneratedTwinScan.S100C08
import Sude.GeneratedTwinScan.S100C09
import Sude.GeneratedTwinScan.S100C10
import Sude.GeneratedTwinScan.S100C11
import Sude.GeneratedTwinScan.S100C12
import Sude.GeneratedTwinScan.S100C13
import Sude.GeneratedTwinScan.S100C14
import Sude.GeneratedTwinScan.S100C15

/-! Combined FT source segment; Lean kernel check required. -/
namespace Sude.GeneratedTwinScan
namespace S100All

theorem join_0_0 : (twinPrimeSegment 209715245 209977389).card = 934 := by
  simpa using combineTwinPrimeSegments (by decide : 209715245 ≤ 209846317)
    (by decide : 209846317 ≤ 209977389) S100C00.total S100C01.total

theorem join_0_1 : (twinPrimeSegment 209977389 210239533).card = 930 := by
  simpa using combineTwinPrimeSegments (by decide : 209977389 ≤ 210108461)
    (by decide : 210108461 ≤ 210239533) S100C02.total S100C03.total

theorem join_0_2 : (twinPrimeSegment 210239533 210501677).card = 958 := by
  simpa using combineTwinPrimeSegments (by decide : 210239533 ≤ 210370605)
    (by decide : 210370605 ≤ 210501677) S100C04.total S100C05.total

theorem join_0_3 : (twinPrimeSegment 210501677 210763821).card = 966 := by
  simpa using combineTwinPrimeSegments (by decide : 210501677 ≤ 210632749)
    (by decide : 210632749 ≤ 210763821) S100C06.total S100C07.total

theorem join_0_4 : (twinPrimeSegment 210763821 211025965).card = 917 := by
  simpa using combineTwinPrimeSegments (by decide : 210763821 ≤ 210894893)
    (by decide : 210894893 ≤ 211025965) S100C08.total S100C09.total

theorem join_0_5 : (twinPrimeSegment 211025965 211288109).card = 904 := by
  simpa using combineTwinPrimeSegments (by decide : 211025965 ≤ 211157037)
    (by decide : 211157037 ≤ 211288109) S100C10.total S100C11.total

theorem join_0_6 : (twinPrimeSegment 211288109 211550253).card = 959 := by
  simpa using combineTwinPrimeSegments (by decide : 211288109 ≤ 211419181)
    (by decide : 211419181 ≤ 211550253) S100C12.total S100C13.total

theorem join_0_7 : (twinPrimeSegment 211550253 211812397).card = 980 := by
  simpa using combineTwinPrimeSegments (by decide : 211550253 ≤ 211681325)
    (by decide : 211681325 ≤ 211812397) S100C14.total S100C15.total

theorem join_1_0 : (twinPrimeSegment 209715245 210239533).card = 1864 := by
  simpa using combineTwinPrimeSegments (by decide : 209715245 ≤ 209977389)
    (by decide : 209977389 ≤ 210239533) join_0_0 join_0_1

theorem join_1_1 : (twinPrimeSegment 210239533 210763821).card = 1924 := by
  simpa using combineTwinPrimeSegments (by decide : 210239533 ≤ 210501677)
    (by decide : 210501677 ≤ 210763821) join_0_2 join_0_3

theorem join_1_2 : (twinPrimeSegment 210763821 211288109).card = 1821 := by
  simpa using combineTwinPrimeSegments (by decide : 210763821 ≤ 211025965)
    (by decide : 211025965 ≤ 211288109) join_0_4 join_0_5

theorem join_1_3 : (twinPrimeSegment 211288109 211812397).card = 1939 := by
  simpa using combineTwinPrimeSegments (by decide : 211288109 ≤ 211550253)
    (by decide : 211550253 ≤ 211812397) join_0_6 join_0_7

theorem join_2_0 : (twinPrimeSegment 209715245 210763821).card = 3788 := by
  simpa using combineTwinPrimeSegments (by decide : 209715245 ≤ 210239533)
    (by decide : 210239533 ≤ 210763821) join_1_0 join_1_1

theorem join_2_1 : (twinPrimeSegment 210763821 211812397).card = 3760 := by
  simpa using combineTwinPrimeSegments (by decide : 210763821 ≤ 211288109)
    (by decide : 211288109 ≤ 211812397) join_1_2 join_1_3

theorem join_3_0 : (twinPrimeSegment 209715245 211812397).card = 7548 := by
  simpa using combineTwinPrimeSegments (by decide : 209715245 ≤ 210763821)
    (by decide : 210763821 ≤ 211812397) join_2_0 join_2_1

theorem total : (twinPrimeSegment 209715245 211812397).card = 7548 := join_3_0

end S100All
end Sude.GeneratedTwinScan
