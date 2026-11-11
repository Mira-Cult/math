import Sude.GeneratedTwinScan.S034C00
import Sude.GeneratedTwinScan.S034C01
import Sude.GeneratedTwinScan.S034C02
import Sude.GeneratedTwinScan.S034C03
import Sude.GeneratedTwinScan.S034C04
import Sude.GeneratedTwinScan.S034C05
import Sude.GeneratedTwinScan.S034C06
import Sude.GeneratedTwinScan.S034C07
import Sude.GeneratedTwinScan.S034C08
import Sude.GeneratedTwinScan.S034C09
import Sude.GeneratedTwinScan.S034C10
import Sude.GeneratedTwinScan.S034C11
import Sude.GeneratedTwinScan.S034C12
import Sude.GeneratedTwinScan.S034C13
import Sude.GeneratedTwinScan.S034C14
import Sude.GeneratedTwinScan.S034C15

/-! Combined FT source segment; Lean kernel check required. -/
namespace Sude.GeneratedTwinScan
namespace S034All

theorem join_0_0 : (twinPrimeSegment 71303213 71565357).card = 1025 := by
  simpa using combineTwinPrimeSegments (by decide : 71303213 ≤ 71434285)
    (by decide : 71434285 ≤ 71565357) S034C00.total S034C01.total

theorem join_0_1 : (twinPrimeSegment 71565357 71827501).card = 1000 := by
  simpa using combineTwinPrimeSegments (by decide : 71565357 ≤ 71696429)
    (by decide : 71696429 ≤ 71827501) S034C02.total S034C03.total

theorem join_0_2 : (twinPrimeSegment 71827501 72089645).card = 1009 := by
  simpa using combineTwinPrimeSegments (by decide : 71827501 ≤ 71958573)
    (by decide : 71958573 ≤ 72089645) S034C04.total S034C05.total

theorem join_0_3 : (twinPrimeSegment 72089645 72351789).card = 1110 := by
  simpa using combineTwinPrimeSegments (by decide : 72089645 ≤ 72220717)
    (by decide : 72220717 ≤ 72351789) S034C06.total S034C07.total

theorem join_0_4 : (twinPrimeSegment 72351789 72613933).card = 1071 := by
  simpa using combineTwinPrimeSegments (by decide : 72351789 ≤ 72482861)
    (by decide : 72482861 ≤ 72613933) S034C08.total S034C09.total

theorem join_0_5 : (twinPrimeSegment 72613933 72876077).card = 1057 := by
  simpa using combineTwinPrimeSegments (by decide : 72613933 ≤ 72745005)
    (by decide : 72745005 ≤ 72876077) S034C10.total S034C11.total

theorem join_0_6 : (twinPrimeSegment 72876077 73138221).card = 1056 := by
  simpa using combineTwinPrimeSegments (by decide : 72876077 ≤ 73007149)
    (by decide : 73007149 ≤ 73138221) S034C12.total S034C13.total

theorem join_0_7 : (twinPrimeSegment 73138221 73400365).card = 1046 := by
  simpa using combineTwinPrimeSegments (by decide : 73138221 ≤ 73269293)
    (by decide : 73269293 ≤ 73400365) S034C14.total S034C15.total

theorem join_1_0 : (twinPrimeSegment 71303213 71827501).card = 2025 := by
  simpa using combineTwinPrimeSegments (by decide : 71303213 ≤ 71565357)
    (by decide : 71565357 ≤ 71827501) join_0_0 join_0_1

theorem join_1_1 : (twinPrimeSegment 71827501 72351789).card = 2119 := by
  simpa using combineTwinPrimeSegments (by decide : 71827501 ≤ 72089645)
    (by decide : 72089645 ≤ 72351789) join_0_2 join_0_3

theorem join_1_2 : (twinPrimeSegment 72351789 72876077).card = 2128 := by
  simpa using combineTwinPrimeSegments (by decide : 72351789 ≤ 72613933)
    (by decide : 72613933 ≤ 72876077) join_0_4 join_0_5

theorem join_1_3 : (twinPrimeSegment 72876077 73400365).card = 2102 := by
  simpa using combineTwinPrimeSegments (by decide : 72876077 ≤ 73138221)
    (by decide : 73138221 ≤ 73400365) join_0_6 join_0_7

theorem join_2_0 : (twinPrimeSegment 71303213 72351789).card = 4144 := by
  simpa using combineTwinPrimeSegments (by decide : 71303213 ≤ 71827501)
    (by decide : 71827501 ≤ 72351789) join_1_0 join_1_1

theorem join_2_1 : (twinPrimeSegment 72351789 73400365).card = 4230 := by
  simpa using combineTwinPrimeSegments (by decide : 72351789 ≤ 72876077)
    (by decide : 72876077 ≤ 73400365) join_1_2 join_1_3

theorem join_3_0 : (twinPrimeSegment 71303213 73400365).card = 8374 := by
  simpa using combineTwinPrimeSegments (by decide : 71303213 ≤ 72351789)
    (by decide : 72351789 ≤ 73400365) join_2_0 join_2_1

theorem total : (twinPrimeSegment 71303213 73400365).card = 8374 := join_3_0

end S034All
end Sude.GeneratedTwinScan
