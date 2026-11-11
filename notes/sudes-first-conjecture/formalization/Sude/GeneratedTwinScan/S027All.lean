import Sude.GeneratedTwinScan.S027C00
import Sude.GeneratedTwinScan.S027C01
import Sude.GeneratedTwinScan.S027C02
import Sude.GeneratedTwinScan.S027C03
import Sude.GeneratedTwinScan.S027C04
import Sude.GeneratedTwinScan.S027C05
import Sude.GeneratedTwinScan.S027C06
import Sude.GeneratedTwinScan.S027C07
import Sude.GeneratedTwinScan.S027C08
import Sude.GeneratedTwinScan.S027C09
import Sude.GeneratedTwinScan.S027C10
import Sude.GeneratedTwinScan.S027C11
import Sude.GeneratedTwinScan.S027C12
import Sude.GeneratedTwinScan.S027C13
import Sude.GeneratedTwinScan.S027C14
import Sude.GeneratedTwinScan.S027C15

/-! Combined FT source segment; Lean kernel check required. -/
namespace Sude.GeneratedTwinScan
namespace S027All

theorem join_0_0 : (twinPrimeSegment 56623149 56885293).card = 1055 := by
  simpa using combineTwinPrimeSegments (by decide : 56623149 ≤ 56754221)
    (by decide : 56754221 ≤ 56885293) S027C00.total S027C01.total

theorem join_0_1 : (twinPrimeSegment 56885293 57147437).card = 1116 := by
  simpa using combineTwinPrimeSegments (by decide : 56885293 ≤ 57016365)
    (by decide : 57016365 ≤ 57147437) S027C02.total S027C03.total

theorem join_0_2 : (twinPrimeSegment 57147437 57409581).card = 1124 := by
  simpa using combineTwinPrimeSegments (by decide : 57147437 ≤ 57278509)
    (by decide : 57278509 ≤ 57409581) S027C04.total S027C05.total

theorem join_0_3 : (twinPrimeSegment 57409581 57671725).card = 1083 := by
  simpa using combineTwinPrimeSegments (by decide : 57409581 ≤ 57540653)
    (by decide : 57540653 ≤ 57671725) S027C06.total S027C07.total

theorem join_0_4 : (twinPrimeSegment 57671725 57933869).card = 1078 := by
  simpa using combineTwinPrimeSegments (by decide : 57671725 ≤ 57802797)
    (by decide : 57802797 ≤ 57933869) S027C08.total S027C09.total

theorem join_0_5 : (twinPrimeSegment 57933869 58196013).card = 1081 := by
  simpa using combineTwinPrimeSegments (by decide : 57933869 ≤ 58064941)
    (by decide : 58064941 ≤ 58196013) S027C10.total S027C11.total

theorem join_0_6 : (twinPrimeSegment 58196013 58458157).card = 1083 := by
  simpa using combineTwinPrimeSegments (by decide : 58196013 ≤ 58327085)
    (by decide : 58327085 ≤ 58458157) S027C12.total S027C13.total

theorem join_0_7 : (twinPrimeSegment 58458157 58720301).card = 1066 := by
  simpa using combineTwinPrimeSegments (by decide : 58458157 ≤ 58589229)
    (by decide : 58589229 ≤ 58720301) S027C14.total S027C15.total

theorem join_1_0 : (twinPrimeSegment 56623149 57147437).card = 2171 := by
  simpa using combineTwinPrimeSegments (by decide : 56623149 ≤ 56885293)
    (by decide : 56885293 ≤ 57147437) join_0_0 join_0_1

theorem join_1_1 : (twinPrimeSegment 57147437 57671725).card = 2207 := by
  simpa using combineTwinPrimeSegments (by decide : 57147437 ≤ 57409581)
    (by decide : 57409581 ≤ 57671725) join_0_2 join_0_3

theorem join_1_2 : (twinPrimeSegment 57671725 58196013).card = 2159 := by
  simpa using combineTwinPrimeSegments (by decide : 57671725 ≤ 57933869)
    (by decide : 57933869 ≤ 58196013) join_0_4 join_0_5

theorem join_1_3 : (twinPrimeSegment 58196013 58720301).card = 2149 := by
  simpa using combineTwinPrimeSegments (by decide : 58196013 ≤ 58458157)
    (by decide : 58458157 ≤ 58720301) join_0_6 join_0_7

theorem join_2_0 : (twinPrimeSegment 56623149 57671725).card = 4378 := by
  simpa using combineTwinPrimeSegments (by decide : 56623149 ≤ 57147437)
    (by decide : 57147437 ≤ 57671725) join_1_0 join_1_1

theorem join_2_1 : (twinPrimeSegment 57671725 58720301).card = 4308 := by
  simpa using combineTwinPrimeSegments (by decide : 57671725 ≤ 58196013)
    (by decide : 58196013 ≤ 58720301) join_1_2 join_1_3

theorem join_3_0 : (twinPrimeSegment 56623149 58720301).card = 8686 := by
  simpa using combineTwinPrimeSegments (by decide : 56623149 ≤ 57671725)
    (by decide : 57671725 ≤ 58720301) join_2_0 join_2_1

theorem total : (twinPrimeSegment 56623149 58720301).card = 8686 := join_3_0

end S027All
end Sude.GeneratedTwinScan
