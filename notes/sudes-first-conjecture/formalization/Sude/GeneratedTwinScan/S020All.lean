import Sude.GeneratedTwinScan.S020C00
import Sude.GeneratedTwinScan.S020C01
import Sude.GeneratedTwinScan.S020C02
import Sude.GeneratedTwinScan.S020C03
import Sude.GeneratedTwinScan.S020C04
import Sude.GeneratedTwinScan.S020C05
import Sude.GeneratedTwinScan.S020C06
import Sude.GeneratedTwinScan.S020C07
import Sude.GeneratedTwinScan.S020C08
import Sude.GeneratedTwinScan.S020C09
import Sude.GeneratedTwinScan.S020C10
import Sude.GeneratedTwinScan.S020C11
import Sude.GeneratedTwinScan.S020C12
import Sude.GeneratedTwinScan.S020C13
import Sude.GeneratedTwinScan.S020C14
import Sude.GeneratedTwinScan.S020C15

/-! Combined FT source segment; Lean kernel check required. -/
namespace Sude.GeneratedTwinScan
namespace S020All

theorem join_0_0 : (twinPrimeSegment 41943085 42205229).card = 1112 := by
  simpa using combineTwinPrimeSegments (by decide : 41943085 ≤ 42074157)
    (by decide : 42074157 ≤ 42205229) S020C00.total S020C01.total

theorem join_0_1 : (twinPrimeSegment 42205229 42467373).card = 1085 := by
  simpa using combineTwinPrimeSegments (by decide : 42205229 ≤ 42336301)
    (by decide : 42336301 ≤ 42467373) S020C02.total S020C03.total

theorem join_0_2 : (twinPrimeSegment 42467373 42729517).card = 1118 := by
  simpa using combineTwinPrimeSegments (by decide : 42467373 ≤ 42598445)
    (by decide : 42598445 ≤ 42729517) S020C04.total S020C05.total

theorem join_0_3 : (twinPrimeSegment 42729517 42991661).card = 1138 := by
  simpa using combineTwinPrimeSegments (by decide : 42729517 ≤ 42860589)
    (by decide : 42860589 ≤ 42991661) S020C06.total S020C07.total

theorem join_0_4 : (twinPrimeSegment 42991661 43253805).card = 1171 := by
  simpa using combineTwinPrimeSegments (by decide : 42991661 ≤ 43122733)
    (by decide : 43122733 ≤ 43253805) S020C08.total S020C09.total

theorem join_0_5 : (twinPrimeSegment 43253805 43515949).card = 1110 := by
  simpa using combineTwinPrimeSegments (by decide : 43253805 ≤ 43384877)
    (by decide : 43384877 ≤ 43515949) S020C10.total S020C11.total

theorem join_0_6 : (twinPrimeSegment 43515949 43778093).card = 1059 := by
  simpa using combineTwinPrimeSegments (by decide : 43515949 ≤ 43647021)
    (by decide : 43647021 ≤ 43778093) S020C12.total S020C13.total

theorem join_0_7 : (twinPrimeSegment 43778093 44040237).card = 1094 := by
  simpa using combineTwinPrimeSegments (by decide : 43778093 ≤ 43909165)
    (by decide : 43909165 ≤ 44040237) S020C14.total S020C15.total

theorem join_1_0 : (twinPrimeSegment 41943085 42467373).card = 2197 := by
  simpa using combineTwinPrimeSegments (by decide : 41943085 ≤ 42205229)
    (by decide : 42205229 ≤ 42467373) join_0_0 join_0_1

theorem join_1_1 : (twinPrimeSegment 42467373 42991661).card = 2256 := by
  simpa using combineTwinPrimeSegments (by decide : 42467373 ≤ 42729517)
    (by decide : 42729517 ≤ 42991661) join_0_2 join_0_3

theorem join_1_2 : (twinPrimeSegment 42991661 43515949).card = 2281 := by
  simpa using combineTwinPrimeSegments (by decide : 42991661 ≤ 43253805)
    (by decide : 43253805 ≤ 43515949) join_0_4 join_0_5

theorem join_1_3 : (twinPrimeSegment 43515949 44040237).card = 2153 := by
  simpa using combineTwinPrimeSegments (by decide : 43515949 ≤ 43778093)
    (by decide : 43778093 ≤ 44040237) join_0_6 join_0_7

theorem join_2_0 : (twinPrimeSegment 41943085 42991661).card = 4453 := by
  simpa using combineTwinPrimeSegments (by decide : 41943085 ≤ 42467373)
    (by decide : 42467373 ≤ 42991661) join_1_0 join_1_1

theorem join_2_1 : (twinPrimeSegment 42991661 44040237).card = 4434 := by
  simpa using combineTwinPrimeSegments (by decide : 42991661 ≤ 43515949)
    (by decide : 43515949 ≤ 44040237) join_1_2 join_1_3

theorem join_3_0 : (twinPrimeSegment 41943085 44040237).card = 8887 := by
  simpa using combineTwinPrimeSegments (by decide : 41943085 ≤ 42991661)
    (by decide : 42991661 ≤ 44040237) join_2_0 join_2_1

theorem total : (twinPrimeSegment 41943085 44040237).card = 8887 := join_3_0

end S020All
end Sude.GeneratedTwinScan
