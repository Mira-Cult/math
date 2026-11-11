import Sude.GeneratedTwinScan.S024C00
import Sude.GeneratedTwinScan.S024C01
import Sude.GeneratedTwinScan.S024C02
import Sude.GeneratedTwinScan.S024C03
import Sude.GeneratedTwinScan.S024C04
import Sude.GeneratedTwinScan.S024C05
import Sude.GeneratedTwinScan.S024C06
import Sude.GeneratedTwinScan.S024C07
import Sude.GeneratedTwinScan.S024C08
import Sude.GeneratedTwinScan.S024C09
import Sude.GeneratedTwinScan.S024C10
import Sude.GeneratedTwinScan.S024C11
import Sude.GeneratedTwinScan.S024C12
import Sude.GeneratedTwinScan.S024C13
import Sude.GeneratedTwinScan.S024C14
import Sude.GeneratedTwinScan.S024C15

/-! Combined FT source segment; Lean kernel check required. -/
namespace Sude.GeneratedTwinScan
namespace S024All

theorem join_0_0 : (twinPrimeSegment 50331693 50593837).card = 1062 := by
  simpa using combineTwinPrimeSegments (by decide : 50331693 ≤ 50462765)
    (by decide : 50462765 ≤ 50593837) S024C00.total S024C01.total

theorem join_0_1 : (twinPrimeSegment 50593837 50855981).card = 1068 := by
  simpa using combineTwinPrimeSegments (by decide : 50593837 ≤ 50724909)
    (by decide : 50724909 ≤ 50855981) S024C02.total S024C03.total

theorem join_0_2 : (twinPrimeSegment 50855981 51118125).card = 1096 := by
  simpa using combineTwinPrimeSegments (by decide : 50855981 ≤ 50987053)
    (by decide : 50987053 ≤ 51118125) S024C04.total S024C05.total

theorem join_0_3 : (twinPrimeSegment 51118125 51380269).card = 1095 := by
  simpa using combineTwinPrimeSegments (by decide : 51118125 ≤ 51249197)
    (by decide : 51249197 ≤ 51380269) S024C06.total S024C07.total

theorem join_0_4 : (twinPrimeSegment 51380269 51642413).card = 1073 := by
  simpa using combineTwinPrimeSegments (by decide : 51380269 ≤ 51511341)
    (by decide : 51511341 ≤ 51642413) S024C08.total S024C09.total

theorem join_0_5 : (twinPrimeSegment 51642413 51904557).card = 1078 := by
  simpa using combineTwinPrimeSegments (by decide : 51642413 ≤ 51773485)
    (by decide : 51773485 ≤ 51904557) S024C10.total S024C11.total

theorem join_0_6 : (twinPrimeSegment 51904557 52166701).card = 1114 := by
  simpa using combineTwinPrimeSegments (by decide : 51904557 ≤ 52035629)
    (by decide : 52035629 ≤ 52166701) S024C12.total S024C13.total

theorem join_0_7 : (twinPrimeSegment 52166701 52428845).card = 1079 := by
  simpa using combineTwinPrimeSegments (by decide : 52166701 ≤ 52297773)
    (by decide : 52297773 ≤ 52428845) S024C14.total S024C15.total

theorem join_1_0 : (twinPrimeSegment 50331693 50855981).card = 2130 := by
  simpa using combineTwinPrimeSegments (by decide : 50331693 ≤ 50593837)
    (by decide : 50593837 ≤ 50855981) join_0_0 join_0_1

theorem join_1_1 : (twinPrimeSegment 50855981 51380269).card = 2191 := by
  simpa using combineTwinPrimeSegments (by decide : 50855981 ≤ 51118125)
    (by decide : 51118125 ≤ 51380269) join_0_2 join_0_3

theorem join_1_2 : (twinPrimeSegment 51380269 51904557).card = 2151 := by
  simpa using combineTwinPrimeSegments (by decide : 51380269 ≤ 51642413)
    (by decide : 51642413 ≤ 51904557) join_0_4 join_0_5

theorem join_1_3 : (twinPrimeSegment 51904557 52428845).card = 2193 := by
  simpa using combineTwinPrimeSegments (by decide : 51904557 ≤ 52166701)
    (by decide : 52166701 ≤ 52428845) join_0_6 join_0_7

theorem join_2_0 : (twinPrimeSegment 50331693 51380269).card = 4321 := by
  simpa using combineTwinPrimeSegments (by decide : 50331693 ≤ 50855981)
    (by decide : 50855981 ≤ 51380269) join_1_0 join_1_1

theorem join_2_1 : (twinPrimeSegment 51380269 52428845).card = 4344 := by
  simpa using combineTwinPrimeSegments (by decide : 51380269 ≤ 51904557)
    (by decide : 51904557 ≤ 52428845) join_1_2 join_1_3

theorem join_3_0 : (twinPrimeSegment 50331693 52428845).card = 8665 := by
  simpa using combineTwinPrimeSegments (by decide : 50331693 ≤ 51380269)
    (by decide : 51380269 ≤ 52428845) join_2_0 join_2_1

theorem total : (twinPrimeSegment 50331693 52428845).card = 8665 := join_3_0

end S024All
end Sude.GeneratedTwinScan
