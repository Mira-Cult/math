import Sude.GeneratedTwinScan.S130C00
import Sude.GeneratedTwinScan.S130C01
import Sude.GeneratedTwinScan.S130C02
import Sude.GeneratedTwinScan.S130C03
import Sude.GeneratedTwinScan.S130C04
import Sude.GeneratedTwinScan.S130C05
import Sude.GeneratedTwinScan.S130C06
import Sude.GeneratedTwinScan.S130C07
import Sude.GeneratedTwinScan.S130C08
import Sude.GeneratedTwinScan.S130C09
import Sude.GeneratedTwinScan.S130C10
import Sude.GeneratedTwinScan.S130C11
import Sude.GeneratedTwinScan.S130C12
import Sude.GeneratedTwinScan.S130C13
import Sude.GeneratedTwinScan.S130C14
import Sude.GeneratedTwinScan.S130C15

/-! Combined FT source segment; Lean kernel check required. -/
namespace Sude.GeneratedTwinScan
namespace S130All

theorem join_0_0 : (twinPrimeSegment 272629805 272891949).card = 859 := by
  simpa using combineTwinPrimeSegments (by decide : 272629805 ≤ 272760877)
    (by decide : 272760877 ≤ 272891949) S130C00.total S130C01.total

theorem join_0_1 : (twinPrimeSegment 272891949 273154093).card = 917 := by
  simpa using combineTwinPrimeSegments (by decide : 272891949 ≤ 273023021)
    (by decide : 273023021 ≤ 273154093) S130C02.total S130C03.total

theorem join_0_2 : (twinPrimeSegment 273154093 273416237).card = 893 := by
  simpa using combineTwinPrimeSegments (by decide : 273154093 ≤ 273285165)
    (by decide : 273285165 ≤ 273416237) S130C04.total S130C05.total

theorem join_0_3 : (twinPrimeSegment 273416237 273678381).card = 906 := by
  simpa using combineTwinPrimeSegments (by decide : 273416237 ≤ 273547309)
    (by decide : 273547309 ≤ 273678381) S130C06.total S130C07.total

theorem join_0_4 : (twinPrimeSegment 273678381 273940525).card = 938 := by
  simpa using combineTwinPrimeSegments (by decide : 273678381 ≤ 273809453)
    (by decide : 273809453 ≤ 273940525) S130C08.total S130C09.total

theorem join_0_5 : (twinPrimeSegment 273940525 274202669).card = 905 := by
  simpa using combineTwinPrimeSegments (by decide : 273940525 ≤ 274071597)
    (by decide : 274071597 ≤ 274202669) S130C10.total S130C11.total

theorem join_0_6 : (twinPrimeSegment 274202669 274464813).card = 949 := by
  simpa using combineTwinPrimeSegments (by decide : 274202669 ≤ 274333741)
    (by decide : 274333741 ≤ 274464813) S130C12.total S130C13.total

theorem join_0_7 : (twinPrimeSegment 274464813 274726957).card = 905 := by
  simpa using combineTwinPrimeSegments (by decide : 274464813 ≤ 274595885)
    (by decide : 274595885 ≤ 274726957) S130C14.total S130C15.total

theorem join_1_0 : (twinPrimeSegment 272629805 273154093).card = 1776 := by
  simpa using combineTwinPrimeSegments (by decide : 272629805 ≤ 272891949)
    (by decide : 272891949 ≤ 273154093) join_0_0 join_0_1

theorem join_1_1 : (twinPrimeSegment 273154093 273678381).card = 1799 := by
  simpa using combineTwinPrimeSegments (by decide : 273154093 ≤ 273416237)
    (by decide : 273416237 ≤ 273678381) join_0_2 join_0_3

theorem join_1_2 : (twinPrimeSegment 273678381 274202669).card = 1843 := by
  simpa using combineTwinPrimeSegments (by decide : 273678381 ≤ 273940525)
    (by decide : 273940525 ≤ 274202669) join_0_4 join_0_5

theorem join_1_3 : (twinPrimeSegment 274202669 274726957).card = 1854 := by
  simpa using combineTwinPrimeSegments (by decide : 274202669 ≤ 274464813)
    (by decide : 274464813 ≤ 274726957) join_0_6 join_0_7

theorem join_2_0 : (twinPrimeSegment 272629805 273678381).card = 3575 := by
  simpa using combineTwinPrimeSegments (by decide : 272629805 ≤ 273154093)
    (by decide : 273154093 ≤ 273678381) join_1_0 join_1_1

theorem join_2_1 : (twinPrimeSegment 273678381 274726957).card = 3697 := by
  simpa using combineTwinPrimeSegments (by decide : 273678381 ≤ 274202669)
    (by decide : 274202669 ≤ 274726957) join_1_2 join_1_3

theorem join_3_0 : (twinPrimeSegment 272629805 274726957).card = 7272 := by
  simpa using combineTwinPrimeSegments (by decide : 272629805 ≤ 273678381)
    (by decide : 273678381 ≤ 274726957) join_2_0 join_2_1

theorem total : (twinPrimeSegment 272629805 274726957).card = 7272 := join_3_0

end S130All
end Sude.GeneratedTwinScan
