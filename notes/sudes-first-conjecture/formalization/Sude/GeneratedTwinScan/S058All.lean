import Sude.GeneratedTwinScan.S058C00
import Sude.GeneratedTwinScan.S058C01
import Sude.GeneratedTwinScan.S058C02
import Sude.GeneratedTwinScan.S058C03
import Sude.GeneratedTwinScan.S058C04
import Sude.GeneratedTwinScan.S058C05
import Sude.GeneratedTwinScan.S058C06
import Sude.GeneratedTwinScan.S058C07
import Sude.GeneratedTwinScan.S058C08
import Sude.GeneratedTwinScan.S058C09
import Sude.GeneratedTwinScan.S058C10
import Sude.GeneratedTwinScan.S058C11
import Sude.GeneratedTwinScan.S058C12
import Sude.GeneratedTwinScan.S058C13
import Sude.GeneratedTwinScan.S058C14
import Sude.GeneratedTwinScan.S058C15

/-! Combined FT source segment; Lean kernel check required. -/
namespace Sude.GeneratedTwinScan
namespace S058All

theorem join_0_0 : (twinPrimeSegment 121634861 121897005).card = 1012 := by
  simpa using combineTwinPrimeSegments (by decide : 121634861 ≤ 121765933)
    (by decide : 121765933 ≤ 121897005) S058C00.total S058C01.total

theorem join_0_1 : (twinPrimeSegment 121897005 122159149).card = 984 := by
  simpa using combineTwinPrimeSegments (by decide : 121897005 ≤ 122028077)
    (by decide : 122028077 ≤ 122159149) S058C02.total S058C03.total

theorem join_0_2 : (twinPrimeSegment 122159149 122421293).card = 954 := by
  simpa using combineTwinPrimeSegments (by decide : 122159149 ≤ 122290221)
    (by decide : 122290221 ≤ 122421293) S058C04.total S058C05.total

theorem join_0_3 : (twinPrimeSegment 122421293 122683437).card = 998 := by
  simpa using combineTwinPrimeSegments (by decide : 122421293 ≤ 122552365)
    (by decide : 122552365 ≤ 122683437) S058C06.total S058C07.total

theorem join_0_4 : (twinPrimeSegment 122683437 122945581).card = 1025 := by
  simpa using combineTwinPrimeSegments (by decide : 122683437 ≤ 122814509)
    (by decide : 122814509 ≤ 122945581) S058C08.total S058C09.total

theorem join_0_5 : (twinPrimeSegment 122945581 123207725).card = 991 := by
  simpa using combineTwinPrimeSegments (by decide : 122945581 ≤ 123076653)
    (by decide : 123076653 ≤ 123207725) S058C10.total S058C11.total

theorem join_0_6 : (twinPrimeSegment 123207725 123469869).card = 1015 := by
  simpa using combineTwinPrimeSegments (by decide : 123207725 ≤ 123338797)
    (by decide : 123338797 ≤ 123469869) S058C12.total S058C13.total

theorem join_0_7 : (twinPrimeSegment 123469869 123732013).card = 1029 := by
  simpa using combineTwinPrimeSegments (by decide : 123469869 ≤ 123600941)
    (by decide : 123600941 ≤ 123732013) S058C14.total S058C15.total

theorem join_1_0 : (twinPrimeSegment 121634861 122159149).card = 1996 := by
  simpa using combineTwinPrimeSegments (by decide : 121634861 ≤ 121897005)
    (by decide : 121897005 ≤ 122159149) join_0_0 join_0_1

theorem join_1_1 : (twinPrimeSegment 122159149 122683437).card = 1952 := by
  simpa using combineTwinPrimeSegments (by decide : 122159149 ≤ 122421293)
    (by decide : 122421293 ≤ 122683437) join_0_2 join_0_3

theorem join_1_2 : (twinPrimeSegment 122683437 123207725).card = 2016 := by
  simpa using combineTwinPrimeSegments (by decide : 122683437 ≤ 122945581)
    (by decide : 122945581 ≤ 123207725) join_0_4 join_0_5

theorem join_1_3 : (twinPrimeSegment 123207725 123732013).card = 2044 := by
  simpa using combineTwinPrimeSegments (by decide : 123207725 ≤ 123469869)
    (by decide : 123469869 ≤ 123732013) join_0_6 join_0_7

theorem join_2_0 : (twinPrimeSegment 121634861 122683437).card = 3948 := by
  simpa using combineTwinPrimeSegments (by decide : 121634861 ≤ 122159149)
    (by decide : 122159149 ≤ 122683437) join_1_0 join_1_1

theorem join_2_1 : (twinPrimeSegment 122683437 123732013).card = 4060 := by
  simpa using combineTwinPrimeSegments (by decide : 122683437 ≤ 123207725)
    (by decide : 123207725 ≤ 123732013) join_1_2 join_1_3

theorem join_3_0 : (twinPrimeSegment 121634861 123732013).card = 8008 := by
  simpa using combineTwinPrimeSegments (by decide : 121634861 ≤ 122683437)
    (by decide : 122683437 ≤ 123732013) join_2_0 join_2_1

theorem total : (twinPrimeSegment 121634861 123732013).card = 8008 := join_3_0

end S058All
end Sude.GeneratedTwinScan
