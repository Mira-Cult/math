import Sude.GeneratedTwinScan.S035C00
import Sude.GeneratedTwinScan.S035C01
import Sude.GeneratedTwinScan.S035C02
import Sude.GeneratedTwinScan.S035C03
import Sude.GeneratedTwinScan.S035C04
import Sude.GeneratedTwinScan.S035C05
import Sude.GeneratedTwinScan.S035C06
import Sude.GeneratedTwinScan.S035C07
import Sude.GeneratedTwinScan.S035C08
import Sude.GeneratedTwinScan.S035C09
import Sude.GeneratedTwinScan.S035C10
import Sude.GeneratedTwinScan.S035C11
import Sude.GeneratedTwinScan.S035C12
import Sude.GeneratedTwinScan.S035C13
import Sude.GeneratedTwinScan.S035C14
import Sude.GeneratedTwinScan.S035C15

/-! Combined FT source segment; Lean kernel check required. -/
namespace Sude.GeneratedTwinScan
namespace S035All

theorem join_0_0 : (twinPrimeSegment 73400365 73662509).card = 1035 := by
  simpa using combineTwinPrimeSegments (by decide : 73400365 ≤ 73531437)
    (by decide : 73531437 ≤ 73662509) S035C00.total S035C01.total

theorem join_0_1 : (twinPrimeSegment 73662509 73924653).card = 1119 := by
  simpa using combineTwinPrimeSegments (by decide : 73662509 ≤ 73793581)
    (by decide : 73793581 ≤ 73924653) S035C02.total S035C03.total

theorem join_0_2 : (twinPrimeSegment 73924653 74186797).card = 1065 := by
  simpa using combineTwinPrimeSegments (by decide : 73924653 ≤ 74055725)
    (by decide : 74055725 ≤ 74186797) S035C04.total S035C05.total

theorem join_0_3 : (twinPrimeSegment 74186797 74448941).card = 1062 := by
  simpa using combineTwinPrimeSegments (by decide : 74186797 ≤ 74317869)
    (by decide : 74317869 ≤ 74448941) S035C06.total S035C07.total

theorem join_0_4 : (twinPrimeSegment 74448941 74711085).card = 1007 := by
  simpa using combineTwinPrimeSegments (by decide : 74448941 ≤ 74580013)
    (by decide : 74580013 ≤ 74711085) S035C08.total S035C09.total

theorem join_0_5 : (twinPrimeSegment 74711085 74973229).card = 1063 := by
  simpa using combineTwinPrimeSegments (by decide : 74711085 ≤ 74842157)
    (by decide : 74842157 ≤ 74973229) S035C10.total S035C11.total

theorem join_0_6 : (twinPrimeSegment 74973229 75235373).card = 1038 := by
  simpa using combineTwinPrimeSegments (by decide : 74973229 ≤ 75104301)
    (by decide : 75104301 ≤ 75235373) S035C12.total S035C13.total

theorem join_0_7 : (twinPrimeSegment 75235373 75497517).card = 1056 := by
  simpa using combineTwinPrimeSegments (by decide : 75235373 ≤ 75366445)
    (by decide : 75366445 ≤ 75497517) S035C14.total S035C15.total

theorem join_1_0 : (twinPrimeSegment 73400365 73924653).card = 2154 := by
  simpa using combineTwinPrimeSegments (by decide : 73400365 ≤ 73662509)
    (by decide : 73662509 ≤ 73924653) join_0_0 join_0_1

theorem join_1_1 : (twinPrimeSegment 73924653 74448941).card = 2127 := by
  simpa using combineTwinPrimeSegments (by decide : 73924653 ≤ 74186797)
    (by decide : 74186797 ≤ 74448941) join_0_2 join_0_3

theorem join_1_2 : (twinPrimeSegment 74448941 74973229).card = 2070 := by
  simpa using combineTwinPrimeSegments (by decide : 74448941 ≤ 74711085)
    (by decide : 74711085 ≤ 74973229) join_0_4 join_0_5

theorem join_1_3 : (twinPrimeSegment 74973229 75497517).card = 2094 := by
  simpa using combineTwinPrimeSegments (by decide : 74973229 ≤ 75235373)
    (by decide : 75235373 ≤ 75497517) join_0_6 join_0_7

theorem join_2_0 : (twinPrimeSegment 73400365 74448941).card = 4281 := by
  simpa using combineTwinPrimeSegments (by decide : 73400365 ≤ 73924653)
    (by decide : 73924653 ≤ 74448941) join_1_0 join_1_1

theorem join_2_1 : (twinPrimeSegment 74448941 75497517).card = 4164 := by
  simpa using combineTwinPrimeSegments (by decide : 74448941 ≤ 74973229)
    (by decide : 74973229 ≤ 75497517) join_1_2 join_1_3

theorem join_3_0 : (twinPrimeSegment 73400365 75497517).card = 8445 := by
  simpa using combineTwinPrimeSegments (by decide : 73400365 ≤ 74448941)
    (by decide : 74448941 ≤ 75497517) join_2_0 join_2_1

theorem total : (twinPrimeSegment 73400365 75497517).card = 8445 := join_3_0

end S035All
end Sude.GeneratedTwinScan
