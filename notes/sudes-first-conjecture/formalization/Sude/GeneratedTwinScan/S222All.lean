import Sude.GeneratedTwinScan.S222C00
import Sude.GeneratedTwinScan.S222C01
import Sude.GeneratedTwinScan.S222C02
import Sude.GeneratedTwinScan.S222C03
import Sude.GeneratedTwinScan.S222C04
import Sude.GeneratedTwinScan.S222C05
import Sude.GeneratedTwinScan.S222C06
import Sude.GeneratedTwinScan.S222C07
import Sude.GeneratedTwinScan.S222C08
import Sude.GeneratedTwinScan.S222C09
import Sude.GeneratedTwinScan.S222C10
import Sude.GeneratedTwinScan.S222C11
import Sude.GeneratedTwinScan.S222C12
import Sude.GeneratedTwinScan.S222C13
import Sude.GeneratedTwinScan.S222C14
import Sude.GeneratedTwinScan.S222C15

/-! Combined FT source segment; Lean kernel check required. -/
namespace Sude.GeneratedTwinScan
namespace S222All

theorem join_0_0 : (twinPrimeSegment 465567789 465829933).card = 881 := by
  simpa using combineTwinPrimeSegments (by decide : 465567789 ≤ 465698861)
    (by decide : 465698861 ≤ 465829933) S222C00.total S222C01.total

theorem join_0_1 : (twinPrimeSegment 465829933 466092077).card = 854 := by
  simpa using combineTwinPrimeSegments (by decide : 465829933 ≤ 465961005)
    (by decide : 465961005 ≤ 466092077) S222C02.total S222C03.total

theorem join_0_2 : (twinPrimeSegment 466092077 466354221).card = 867 := by
  simpa using combineTwinPrimeSegments (by decide : 466092077 ≤ 466223149)
    (by decide : 466223149 ≤ 466354221) S222C04.total S222C05.total

theorem join_0_3 : (twinPrimeSegment 466354221 466616365).card = 911 := by
  simpa using combineTwinPrimeSegments (by decide : 466354221 ≤ 466485293)
    (by decide : 466485293 ≤ 466616365) S222C06.total S222C07.total

theorem join_0_4 : (twinPrimeSegment 466616365 466878509).card = 859 := by
  simpa using combineTwinPrimeSegments (by decide : 466616365 ≤ 466747437)
    (by decide : 466747437 ≤ 466878509) S222C08.total S222C09.total

theorem join_0_5 : (twinPrimeSegment 466878509 467140653).card = 875 := by
  simpa using combineTwinPrimeSegments (by decide : 466878509 ≤ 467009581)
    (by decide : 467009581 ≤ 467140653) S222C10.total S222C11.total

theorem join_0_6 : (twinPrimeSegment 467140653 467402797).card = 888 := by
  simpa using combineTwinPrimeSegments (by decide : 467140653 ≤ 467271725)
    (by decide : 467271725 ≤ 467402797) S222C12.total S222C13.total

theorem join_0_7 : (twinPrimeSegment 467402797 467664941).card = 918 := by
  simpa using combineTwinPrimeSegments (by decide : 467402797 ≤ 467533869)
    (by decide : 467533869 ≤ 467664941) S222C14.total S222C15.total

theorem join_1_0 : (twinPrimeSegment 465567789 466092077).card = 1735 := by
  simpa using combineTwinPrimeSegments (by decide : 465567789 ≤ 465829933)
    (by decide : 465829933 ≤ 466092077) join_0_0 join_0_1

theorem join_1_1 : (twinPrimeSegment 466092077 466616365).card = 1778 := by
  simpa using combineTwinPrimeSegments (by decide : 466092077 ≤ 466354221)
    (by decide : 466354221 ≤ 466616365) join_0_2 join_0_3

theorem join_1_2 : (twinPrimeSegment 466616365 467140653).card = 1734 := by
  simpa using combineTwinPrimeSegments (by decide : 466616365 ≤ 466878509)
    (by decide : 466878509 ≤ 467140653) join_0_4 join_0_5

theorem join_1_3 : (twinPrimeSegment 467140653 467664941).card = 1806 := by
  simpa using combineTwinPrimeSegments (by decide : 467140653 ≤ 467402797)
    (by decide : 467402797 ≤ 467664941) join_0_6 join_0_7

theorem join_2_0 : (twinPrimeSegment 465567789 466616365).card = 3513 := by
  simpa using combineTwinPrimeSegments (by decide : 465567789 ≤ 466092077)
    (by decide : 466092077 ≤ 466616365) join_1_0 join_1_1

theorem join_2_1 : (twinPrimeSegment 466616365 467664941).card = 3540 := by
  simpa using combineTwinPrimeSegments (by decide : 466616365 ≤ 467140653)
    (by decide : 467140653 ≤ 467664941) join_1_2 join_1_3

theorem join_3_0 : (twinPrimeSegment 465567789 467664941).card = 7053 := by
  simpa using combineTwinPrimeSegments (by decide : 465567789 ≤ 466616365)
    (by decide : 466616365 ≤ 467664941) join_2_0 join_2_1

theorem total : (twinPrimeSegment 465567789 467664941).card = 7053 := join_3_0

end S222All
end Sude.GeneratedTwinScan
