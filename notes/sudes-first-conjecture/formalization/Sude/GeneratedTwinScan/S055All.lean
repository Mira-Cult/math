import Sude.GeneratedTwinScan.S055C00
import Sude.GeneratedTwinScan.S055C01
import Sude.GeneratedTwinScan.S055C02
import Sude.GeneratedTwinScan.S055C03
import Sude.GeneratedTwinScan.S055C04
import Sude.GeneratedTwinScan.S055C05
import Sude.GeneratedTwinScan.S055C06
import Sude.GeneratedTwinScan.S055C07
import Sude.GeneratedTwinScan.S055C08
import Sude.GeneratedTwinScan.S055C09
import Sude.GeneratedTwinScan.S055C10
import Sude.GeneratedTwinScan.S055C11
import Sude.GeneratedTwinScan.S055C12
import Sude.GeneratedTwinScan.S055C13
import Sude.GeneratedTwinScan.S055C14
import Sude.GeneratedTwinScan.S055C15

/-! Combined FT source segment; Lean kernel check required. -/
namespace Sude.GeneratedTwinScan
namespace S055All

theorem join_0_0 : (twinPrimeSegment 115343405 115605549).card = 985 := by
  simpa using combineTwinPrimeSegments (by decide : 115343405 ≤ 115474477)
    (by decide : 115474477 ≤ 115605549) S055C00.total S055C01.total

theorem join_0_1 : (twinPrimeSegment 115605549 115867693).card = 1013 := by
  simpa using combineTwinPrimeSegments (by decide : 115605549 ≤ 115736621)
    (by decide : 115736621 ≤ 115867693) S055C02.total S055C03.total

theorem join_0_2 : (twinPrimeSegment 115867693 116129837).card = 1031 := by
  simpa using combineTwinPrimeSegments (by decide : 115867693 ≤ 115998765)
    (by decide : 115998765 ≤ 116129837) S055C04.total S055C05.total

theorem join_0_3 : (twinPrimeSegment 116129837 116391981).card = 1026 := by
  simpa using combineTwinPrimeSegments (by decide : 116129837 ≤ 116260909)
    (by decide : 116260909 ≤ 116391981) S055C06.total S055C07.total

theorem join_0_4 : (twinPrimeSegment 116391981 116654125).card = 964 := by
  simpa using combineTwinPrimeSegments (by decide : 116391981 ≤ 116523053)
    (by decide : 116523053 ≤ 116654125) S055C08.total S055C09.total

theorem join_0_5 : (twinPrimeSegment 116654125 116916269).card = 1007 := by
  simpa using combineTwinPrimeSegments (by decide : 116654125 ≤ 116785197)
    (by decide : 116785197 ≤ 116916269) S055C10.total S055C11.total

theorem join_0_6 : (twinPrimeSegment 116916269 117178413).card = 998 := by
  simpa using combineTwinPrimeSegments (by decide : 116916269 ≤ 117047341)
    (by decide : 117047341 ≤ 117178413) S055C12.total S055C13.total

theorem join_0_7 : (twinPrimeSegment 117178413 117440557).card = 1000 := by
  simpa using combineTwinPrimeSegments (by decide : 117178413 ≤ 117309485)
    (by decide : 117309485 ≤ 117440557) S055C14.total S055C15.total

theorem join_1_0 : (twinPrimeSegment 115343405 115867693).card = 1998 := by
  simpa using combineTwinPrimeSegments (by decide : 115343405 ≤ 115605549)
    (by decide : 115605549 ≤ 115867693) join_0_0 join_0_1

theorem join_1_1 : (twinPrimeSegment 115867693 116391981).card = 2057 := by
  simpa using combineTwinPrimeSegments (by decide : 115867693 ≤ 116129837)
    (by decide : 116129837 ≤ 116391981) join_0_2 join_0_3

theorem join_1_2 : (twinPrimeSegment 116391981 116916269).card = 1971 := by
  simpa using combineTwinPrimeSegments (by decide : 116391981 ≤ 116654125)
    (by decide : 116654125 ≤ 116916269) join_0_4 join_0_5

theorem join_1_3 : (twinPrimeSegment 116916269 117440557).card = 1998 := by
  simpa using combineTwinPrimeSegments (by decide : 116916269 ≤ 117178413)
    (by decide : 117178413 ≤ 117440557) join_0_6 join_0_7

theorem join_2_0 : (twinPrimeSegment 115343405 116391981).card = 4055 := by
  simpa using combineTwinPrimeSegments (by decide : 115343405 ≤ 115867693)
    (by decide : 115867693 ≤ 116391981) join_1_0 join_1_1

theorem join_2_1 : (twinPrimeSegment 116391981 117440557).card = 3969 := by
  simpa using combineTwinPrimeSegments (by decide : 116391981 ≤ 116916269)
    (by decide : 116916269 ≤ 117440557) join_1_2 join_1_3

theorem join_3_0 : (twinPrimeSegment 115343405 117440557).card = 8024 := by
  simpa using combineTwinPrimeSegments (by decide : 115343405 ≤ 116391981)
    (by decide : 116391981 ≤ 117440557) join_2_0 join_2_1

theorem total : (twinPrimeSegment 115343405 117440557).card = 8024 := join_3_0

end S055All
end Sude.GeneratedTwinScan
