import Sude.GeneratedTwinScan.S011C00
import Sude.GeneratedTwinScan.S011C01
import Sude.GeneratedTwinScan.S011C02
import Sude.GeneratedTwinScan.S011C03
import Sude.GeneratedTwinScan.S011C04
import Sude.GeneratedTwinScan.S011C05
import Sude.GeneratedTwinScan.S011C06
import Sude.GeneratedTwinScan.S011C07
import Sude.GeneratedTwinScan.S011C08
import Sude.GeneratedTwinScan.S011C09
import Sude.GeneratedTwinScan.S011C10
import Sude.GeneratedTwinScan.S011C11
import Sude.GeneratedTwinScan.S011C12
import Sude.GeneratedTwinScan.S011C13
import Sude.GeneratedTwinScan.S011C14
import Sude.GeneratedTwinScan.S011C15

/-! Combined FT source segment; Lean kernel check required. -/
namespace Sude.GeneratedTwinScan
namespace S011All

theorem join_0_0 : (twinPrimeSegment 23068717 23330861).card = 1205 := by
  simpa using combineTwinPrimeSegments (by decide : 23068717 ≤ 23199789)
    (by decide : 23199789 ≤ 23330861) S011C00.total S011C01.total

theorem join_0_1 : (twinPrimeSegment 23330861 23593005).card = 1234 := by
  simpa using combineTwinPrimeSegments (by decide : 23330861 ≤ 23461933)
    (by decide : 23461933 ≤ 23593005) S011C02.total S011C03.total

theorem join_0_2 : (twinPrimeSegment 23593005 23855149).card = 1176 := by
  simpa using combineTwinPrimeSegments (by decide : 23593005 ≤ 23724077)
    (by decide : 23724077 ≤ 23855149) S011C04.total S011C05.total

theorem join_0_3 : (twinPrimeSegment 23855149 24117293).card = 1230 := by
  simpa using combineTwinPrimeSegments (by decide : 23855149 ≤ 23986221)
    (by decide : 23986221 ≤ 24117293) S011C06.total S011C07.total

theorem join_0_4 : (twinPrimeSegment 24117293 24379437).card = 1215 := by
  simpa using combineTwinPrimeSegments (by decide : 24117293 ≤ 24248365)
    (by decide : 24248365 ≤ 24379437) S011C08.total S011C09.total

theorem join_0_5 : (twinPrimeSegment 24379437 24641581).card = 1177 := by
  simpa using combineTwinPrimeSegments (by decide : 24379437 ≤ 24510509)
    (by decide : 24510509 ≤ 24641581) S011C10.total S011C11.total

theorem join_0_6 : (twinPrimeSegment 24641581 24903725).card = 1200 := by
  simpa using combineTwinPrimeSegments (by decide : 24641581 ≤ 24772653)
    (by decide : 24772653 ≤ 24903725) S011C12.total S011C13.total

theorem join_0_7 : (twinPrimeSegment 24903725 25165869).card = 1189 := by
  simpa using combineTwinPrimeSegments (by decide : 24903725 ≤ 25034797)
    (by decide : 25034797 ≤ 25165869) S011C14.total S011C15.total

theorem join_1_0 : (twinPrimeSegment 23068717 23593005).card = 2439 := by
  simpa using combineTwinPrimeSegments (by decide : 23068717 ≤ 23330861)
    (by decide : 23330861 ≤ 23593005) join_0_0 join_0_1

theorem join_1_1 : (twinPrimeSegment 23593005 24117293).card = 2406 := by
  simpa using combineTwinPrimeSegments (by decide : 23593005 ≤ 23855149)
    (by decide : 23855149 ≤ 24117293) join_0_2 join_0_3

theorem join_1_2 : (twinPrimeSegment 24117293 24641581).card = 2392 := by
  simpa using combineTwinPrimeSegments (by decide : 24117293 ≤ 24379437)
    (by decide : 24379437 ≤ 24641581) join_0_4 join_0_5

theorem join_1_3 : (twinPrimeSegment 24641581 25165869).card = 2389 := by
  simpa using combineTwinPrimeSegments (by decide : 24641581 ≤ 24903725)
    (by decide : 24903725 ≤ 25165869) join_0_6 join_0_7

theorem join_2_0 : (twinPrimeSegment 23068717 24117293).card = 4845 := by
  simpa using combineTwinPrimeSegments (by decide : 23068717 ≤ 23593005)
    (by decide : 23593005 ≤ 24117293) join_1_0 join_1_1

theorem join_2_1 : (twinPrimeSegment 24117293 25165869).card = 4781 := by
  simpa using combineTwinPrimeSegments (by decide : 24117293 ≤ 24641581)
    (by decide : 24641581 ≤ 25165869) join_1_2 join_1_3

theorem join_3_0 : (twinPrimeSegment 23068717 25165869).card = 9626 := by
  simpa using combineTwinPrimeSegments (by decide : 23068717 ≤ 24117293)
    (by decide : 24117293 ≤ 25165869) join_2_0 join_2_1

theorem total : (twinPrimeSegment 23068717 25165869).card = 9626 := join_3_0

end S011All
end Sude.GeneratedTwinScan
