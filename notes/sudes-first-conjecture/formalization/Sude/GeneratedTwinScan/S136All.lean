import Sude.GeneratedTwinScan.S136C00
import Sude.GeneratedTwinScan.S136C01
import Sude.GeneratedTwinScan.S136C02
import Sude.GeneratedTwinScan.S136C03
import Sude.GeneratedTwinScan.S136C04
import Sude.GeneratedTwinScan.S136C05
import Sude.GeneratedTwinScan.S136C06
import Sude.GeneratedTwinScan.S136C07
import Sude.GeneratedTwinScan.S136C08
import Sude.GeneratedTwinScan.S136C09
import Sude.GeneratedTwinScan.S136C10
import Sude.GeneratedTwinScan.S136C11
import Sude.GeneratedTwinScan.S136C12
import Sude.GeneratedTwinScan.S136C13
import Sude.GeneratedTwinScan.S136C14
import Sude.GeneratedTwinScan.S136C15

/-! Combined FT source segment; Lean kernel check required. -/
namespace Sude.GeneratedTwinScan
namespace S136All

theorem join_0_0 : (twinPrimeSegment 285212717 285474861).card = 910 := by
  simpa using combineTwinPrimeSegments (by decide : 285212717 ≤ 285343789)
    (by decide : 285343789 ≤ 285474861) S136C00.total S136C01.total

theorem join_0_1 : (twinPrimeSegment 285474861 285737005).card = 942 := by
  simpa using combineTwinPrimeSegments (by decide : 285474861 ≤ 285605933)
    (by decide : 285605933 ≤ 285737005) S136C02.total S136C03.total

theorem join_0_2 : (twinPrimeSegment 285737005 285999149).card = 921 := by
  simpa using combineTwinPrimeSegments (by decide : 285737005 ≤ 285868077)
    (by decide : 285868077 ≤ 285999149) S136C04.total S136C05.total

theorem join_0_3 : (twinPrimeSegment 285999149 286261293).card = 933 := by
  simpa using combineTwinPrimeSegments (by decide : 285999149 ≤ 286130221)
    (by decide : 286130221 ≤ 286261293) S136C06.total S136C07.total

theorem join_0_4 : (twinPrimeSegment 286261293 286523437).card = 949 := by
  simpa using combineTwinPrimeSegments (by decide : 286261293 ≤ 286392365)
    (by decide : 286392365 ≤ 286523437) S136C08.total S136C09.total

theorem join_0_5 : (twinPrimeSegment 286523437 286785581).card = 890 := by
  simpa using combineTwinPrimeSegments (by decide : 286523437 ≤ 286654509)
    (by decide : 286654509 ≤ 286785581) S136C10.total S136C11.total

theorem join_0_6 : (twinPrimeSegment 286785581 287047725).card = 889 := by
  simpa using combineTwinPrimeSegments (by decide : 286785581 ≤ 286916653)
    (by decide : 286916653 ≤ 287047725) S136C12.total S136C13.total

theorem join_0_7 : (twinPrimeSegment 287047725 287309869).card = 932 := by
  simpa using combineTwinPrimeSegments (by decide : 287047725 ≤ 287178797)
    (by decide : 287178797 ≤ 287309869) S136C14.total S136C15.total

theorem join_1_0 : (twinPrimeSegment 285212717 285737005).card = 1852 := by
  simpa using combineTwinPrimeSegments (by decide : 285212717 ≤ 285474861)
    (by decide : 285474861 ≤ 285737005) join_0_0 join_0_1

theorem join_1_1 : (twinPrimeSegment 285737005 286261293).card = 1854 := by
  simpa using combineTwinPrimeSegments (by decide : 285737005 ≤ 285999149)
    (by decide : 285999149 ≤ 286261293) join_0_2 join_0_3

theorem join_1_2 : (twinPrimeSegment 286261293 286785581).card = 1839 := by
  simpa using combineTwinPrimeSegments (by decide : 286261293 ≤ 286523437)
    (by decide : 286523437 ≤ 286785581) join_0_4 join_0_5

theorem join_1_3 : (twinPrimeSegment 286785581 287309869).card = 1821 := by
  simpa using combineTwinPrimeSegments (by decide : 286785581 ≤ 287047725)
    (by decide : 287047725 ≤ 287309869) join_0_6 join_0_7

theorem join_2_0 : (twinPrimeSegment 285212717 286261293).card = 3706 := by
  simpa using combineTwinPrimeSegments (by decide : 285212717 ≤ 285737005)
    (by decide : 285737005 ≤ 286261293) join_1_0 join_1_1

theorem join_2_1 : (twinPrimeSegment 286261293 287309869).card = 3660 := by
  simpa using combineTwinPrimeSegments (by decide : 286261293 ≤ 286785581)
    (by decide : 286785581 ≤ 287309869) join_1_2 join_1_3

theorem join_3_0 : (twinPrimeSegment 285212717 287309869).card = 7366 := by
  simpa using combineTwinPrimeSegments (by decide : 285212717 ≤ 286261293)
    (by decide : 286261293 ≤ 287309869) join_2_0 join_2_1

theorem total : (twinPrimeSegment 285212717 287309869).card = 7366 := join_3_0

end S136All
end Sude.GeneratedTwinScan
