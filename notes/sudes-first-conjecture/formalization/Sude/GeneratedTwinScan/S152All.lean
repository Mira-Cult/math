import Sude.GeneratedTwinScan.S152C00
import Sude.GeneratedTwinScan.S152C01
import Sude.GeneratedTwinScan.S152C02
import Sude.GeneratedTwinScan.S152C03
import Sude.GeneratedTwinScan.S152C04
import Sude.GeneratedTwinScan.S152C05
import Sude.GeneratedTwinScan.S152C06
import Sude.GeneratedTwinScan.S152C07
import Sude.GeneratedTwinScan.S152C08
import Sude.GeneratedTwinScan.S152C09
import Sude.GeneratedTwinScan.S152C10
import Sude.GeneratedTwinScan.S152C11
import Sude.GeneratedTwinScan.S152C12
import Sude.GeneratedTwinScan.S152C13
import Sude.GeneratedTwinScan.S152C14
import Sude.GeneratedTwinScan.S152C15

/-! Combined FT source segment; Lean kernel check required. -/
namespace Sude.GeneratedTwinScan
namespace S152All

theorem join_0_0 : (twinPrimeSegment 318767149 319029293).card = 901 := by
  simpa using combineTwinPrimeSegments (by decide : 318767149 ≤ 318898221)
    (by decide : 318898221 ≤ 319029293) S152C00.total S152C01.total

theorem join_0_1 : (twinPrimeSegment 319029293 319291437).card = 888 := by
  simpa using combineTwinPrimeSegments (by decide : 319029293 ≤ 319160365)
    (by decide : 319160365 ≤ 319291437) S152C02.total S152C03.total

theorem join_0_2 : (twinPrimeSegment 319291437 319553581).card = 917 := by
  simpa using combineTwinPrimeSegments (by decide : 319291437 ≤ 319422509)
    (by decide : 319422509 ≤ 319553581) S152C04.total S152C05.total

theorem join_0_3 : (twinPrimeSegment 319553581 319815725).card = 975 := by
  simpa using combineTwinPrimeSegments (by decide : 319553581 ≤ 319684653)
    (by decide : 319684653 ≤ 319815725) S152C06.total S152C07.total

theorem join_0_4 : (twinPrimeSegment 319815725 320077869).card = 918 := by
  simpa using combineTwinPrimeSegments (by decide : 319815725 ≤ 319946797)
    (by decide : 319946797 ≤ 320077869) S152C08.total S152C09.total

theorem join_0_5 : (twinPrimeSegment 320077869 320340013).card = 902 := by
  simpa using combineTwinPrimeSegments (by decide : 320077869 ≤ 320208941)
    (by decide : 320208941 ≤ 320340013) S152C10.total S152C11.total

theorem join_0_6 : (twinPrimeSegment 320340013 320602157).card = 878 := by
  simpa using combineTwinPrimeSegments (by decide : 320340013 ≤ 320471085)
    (by decide : 320471085 ≤ 320602157) S152C12.total S152C13.total

theorem join_0_7 : (twinPrimeSegment 320602157 320864301).card = 920 := by
  simpa using combineTwinPrimeSegments (by decide : 320602157 ≤ 320733229)
    (by decide : 320733229 ≤ 320864301) S152C14.total S152C15.total

theorem join_1_0 : (twinPrimeSegment 318767149 319291437).card = 1789 := by
  simpa using combineTwinPrimeSegments (by decide : 318767149 ≤ 319029293)
    (by decide : 319029293 ≤ 319291437) join_0_0 join_0_1

theorem join_1_1 : (twinPrimeSegment 319291437 319815725).card = 1892 := by
  simpa using combineTwinPrimeSegments (by decide : 319291437 ≤ 319553581)
    (by decide : 319553581 ≤ 319815725) join_0_2 join_0_3

theorem join_1_2 : (twinPrimeSegment 319815725 320340013).card = 1820 := by
  simpa using combineTwinPrimeSegments (by decide : 319815725 ≤ 320077869)
    (by decide : 320077869 ≤ 320340013) join_0_4 join_0_5

theorem join_1_3 : (twinPrimeSegment 320340013 320864301).card = 1798 := by
  simpa using combineTwinPrimeSegments (by decide : 320340013 ≤ 320602157)
    (by decide : 320602157 ≤ 320864301) join_0_6 join_0_7

theorem join_2_0 : (twinPrimeSegment 318767149 319815725).card = 3681 := by
  simpa using combineTwinPrimeSegments (by decide : 318767149 ≤ 319291437)
    (by decide : 319291437 ≤ 319815725) join_1_0 join_1_1

theorem join_2_1 : (twinPrimeSegment 319815725 320864301).card = 3618 := by
  simpa using combineTwinPrimeSegments (by decide : 319815725 ≤ 320340013)
    (by decide : 320340013 ≤ 320864301) join_1_2 join_1_3

theorem join_3_0 : (twinPrimeSegment 318767149 320864301).card = 7299 := by
  simpa using combineTwinPrimeSegments (by decide : 318767149 ≤ 319815725)
    (by decide : 319815725 ≤ 320864301) join_2_0 join_2_1

theorem total : (twinPrimeSegment 318767149 320864301).card = 7299 := join_3_0

end S152All
end Sude.GeneratedTwinScan
