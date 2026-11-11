import Sude.GeneratedTwinScan.S023C00
import Sude.GeneratedTwinScan.S023C01
import Sude.GeneratedTwinScan.S023C02
import Sude.GeneratedTwinScan.S023C03
import Sude.GeneratedTwinScan.S023C04
import Sude.GeneratedTwinScan.S023C05
import Sude.GeneratedTwinScan.S023C06
import Sude.GeneratedTwinScan.S023C07
import Sude.GeneratedTwinScan.S023C08
import Sude.GeneratedTwinScan.S023C09
import Sude.GeneratedTwinScan.S023C10
import Sude.GeneratedTwinScan.S023C11
import Sude.GeneratedTwinScan.S023C12
import Sude.GeneratedTwinScan.S023C13
import Sude.GeneratedTwinScan.S023C14
import Sude.GeneratedTwinScan.S023C15

/-! Combined FT source segment; Lean kernel check required. -/
namespace Sude.GeneratedTwinScan
namespace S023All

theorem join_0_0 : (twinPrimeSegment 48234541 48496685).card = 1125 := by
  simpa using combineTwinPrimeSegments (by decide : 48234541 ≤ 48365613)
    (by decide : 48365613 ≤ 48496685) S023C00.total S023C01.total

theorem join_0_1 : (twinPrimeSegment 48496685 48758829).card = 1090 := by
  simpa using combineTwinPrimeSegments (by decide : 48496685 ≤ 48627757)
    (by decide : 48627757 ≤ 48758829) S023C02.total S023C03.total

theorem join_0_2 : (twinPrimeSegment 48758829 49020973).card = 1099 := by
  simpa using combineTwinPrimeSegments (by decide : 48758829 ≤ 48889901)
    (by decide : 48889901 ≤ 49020973) S023C04.total S023C05.total

theorem join_0_3 : (twinPrimeSegment 49020973 49283117).card = 1121 := by
  simpa using combineTwinPrimeSegments (by decide : 49020973 ≤ 49152045)
    (by decide : 49152045 ≤ 49283117) S023C06.total S023C07.total

theorem join_0_4 : (twinPrimeSegment 49283117 49545261).card = 1125 := by
  simpa using combineTwinPrimeSegments (by decide : 49283117 ≤ 49414189)
    (by decide : 49414189 ≤ 49545261) S023C08.total S023C09.total

theorem join_0_5 : (twinPrimeSegment 49545261 49807405).card = 1123 := by
  simpa using combineTwinPrimeSegments (by decide : 49545261 ≤ 49676333)
    (by decide : 49676333 ≤ 49807405) S023C10.total S023C11.total

theorem join_0_6 : (twinPrimeSegment 49807405 50069549).card = 1063 := by
  simpa using combineTwinPrimeSegments (by decide : 49807405 ≤ 49938477)
    (by decide : 49938477 ≤ 50069549) S023C12.total S023C13.total

theorem join_0_7 : (twinPrimeSegment 50069549 50331693).card = 1032 := by
  simpa using combineTwinPrimeSegments (by decide : 50069549 ≤ 50200621)
    (by decide : 50200621 ≤ 50331693) S023C14.total S023C15.total

theorem join_1_0 : (twinPrimeSegment 48234541 48758829).card = 2215 := by
  simpa using combineTwinPrimeSegments (by decide : 48234541 ≤ 48496685)
    (by decide : 48496685 ≤ 48758829) join_0_0 join_0_1

theorem join_1_1 : (twinPrimeSegment 48758829 49283117).card = 2220 := by
  simpa using combineTwinPrimeSegments (by decide : 48758829 ≤ 49020973)
    (by decide : 49020973 ≤ 49283117) join_0_2 join_0_3

theorem join_1_2 : (twinPrimeSegment 49283117 49807405).card = 2248 := by
  simpa using combineTwinPrimeSegments (by decide : 49283117 ≤ 49545261)
    (by decide : 49545261 ≤ 49807405) join_0_4 join_0_5

theorem join_1_3 : (twinPrimeSegment 49807405 50331693).card = 2095 := by
  simpa using combineTwinPrimeSegments (by decide : 49807405 ≤ 50069549)
    (by decide : 50069549 ≤ 50331693) join_0_6 join_0_7

theorem join_2_0 : (twinPrimeSegment 48234541 49283117).card = 4435 := by
  simpa using combineTwinPrimeSegments (by decide : 48234541 ≤ 48758829)
    (by decide : 48758829 ≤ 49283117) join_1_0 join_1_1

theorem join_2_1 : (twinPrimeSegment 49283117 50331693).card = 4343 := by
  simpa using combineTwinPrimeSegments (by decide : 49283117 ≤ 49807405)
    (by decide : 49807405 ≤ 50331693) join_1_2 join_1_3

theorem join_3_0 : (twinPrimeSegment 48234541 50331693).card = 8778 := by
  simpa using combineTwinPrimeSegments (by decide : 48234541 ≤ 49283117)
    (by decide : 49283117 ≤ 50331693) join_2_0 join_2_1

theorem total : (twinPrimeSegment 48234541 50331693).card = 8778 := join_3_0

end S023All
end Sude.GeneratedTwinScan
