import Sude.GeneratedTwinScan.S050C00
import Sude.GeneratedTwinScan.S050C01
import Sude.GeneratedTwinScan.S050C02
import Sude.GeneratedTwinScan.S050C03
import Sude.GeneratedTwinScan.S050C04
import Sude.GeneratedTwinScan.S050C05
import Sude.GeneratedTwinScan.S050C06
import Sude.GeneratedTwinScan.S050C07
import Sude.GeneratedTwinScan.S050C08
import Sude.GeneratedTwinScan.S050C09
import Sude.GeneratedTwinScan.S050C10
import Sude.GeneratedTwinScan.S050C11
import Sude.GeneratedTwinScan.S050C12
import Sude.GeneratedTwinScan.S050C13
import Sude.GeneratedTwinScan.S050C14
import Sude.GeneratedTwinScan.S050C15

/-! Combined FT source segment; Lean kernel check required. -/
namespace Sude.GeneratedTwinScan
namespace S050All

theorem join_0_0 : (twinPrimeSegment 104857645 105119789).card = 1070 := by
  simpa using combineTwinPrimeSegments (by decide : 104857645 ≤ 104988717)
    (by decide : 104988717 ≤ 105119789) S050C00.total S050C01.total

theorem join_0_1 : (twinPrimeSegment 105119789 105381933).card = 1031 := by
  simpa using combineTwinPrimeSegments (by decide : 105119789 ≤ 105250861)
    (by decide : 105250861 ≤ 105381933) S050C02.total S050C03.total

theorem join_0_2 : (twinPrimeSegment 105381933 105644077).card = 1013 := by
  simpa using combineTwinPrimeSegments (by decide : 105381933 ≤ 105513005)
    (by decide : 105513005 ≤ 105644077) S050C04.total S050C05.total

theorem join_0_3 : (twinPrimeSegment 105644077 105906221).card = 982 := by
  simpa using combineTwinPrimeSegments (by decide : 105644077 ≤ 105775149)
    (by decide : 105775149 ≤ 105906221) S050C06.total S050C07.total

theorem join_0_4 : (twinPrimeSegment 105906221 106168365).card = 1061 := by
  simpa using combineTwinPrimeSegments (by decide : 105906221 ≤ 106037293)
    (by decide : 106037293 ≤ 106168365) S050C08.total S050C09.total

theorem join_0_5 : (twinPrimeSegment 106168365 106430509).card = 1031 := by
  simpa using combineTwinPrimeSegments (by decide : 106168365 ≤ 106299437)
    (by decide : 106299437 ≤ 106430509) S050C10.total S050C11.total

theorem join_0_6 : (twinPrimeSegment 106430509 106692653).card = 1048 := by
  simpa using combineTwinPrimeSegments (by decide : 106430509 ≤ 106561581)
    (by decide : 106561581 ≤ 106692653) S050C12.total S050C13.total

theorem join_0_7 : (twinPrimeSegment 106692653 106954797).card = 967 := by
  simpa using combineTwinPrimeSegments (by decide : 106692653 ≤ 106823725)
    (by decide : 106823725 ≤ 106954797) S050C14.total S050C15.total

theorem join_1_0 : (twinPrimeSegment 104857645 105381933).card = 2101 := by
  simpa using combineTwinPrimeSegments (by decide : 104857645 ≤ 105119789)
    (by decide : 105119789 ≤ 105381933) join_0_0 join_0_1

theorem join_1_1 : (twinPrimeSegment 105381933 105906221).card = 1995 := by
  simpa using combineTwinPrimeSegments (by decide : 105381933 ≤ 105644077)
    (by decide : 105644077 ≤ 105906221) join_0_2 join_0_3

theorem join_1_2 : (twinPrimeSegment 105906221 106430509).card = 2092 := by
  simpa using combineTwinPrimeSegments (by decide : 105906221 ≤ 106168365)
    (by decide : 106168365 ≤ 106430509) join_0_4 join_0_5

theorem join_1_3 : (twinPrimeSegment 106430509 106954797).card = 2015 := by
  simpa using combineTwinPrimeSegments (by decide : 106430509 ≤ 106692653)
    (by decide : 106692653 ≤ 106954797) join_0_6 join_0_7

theorem join_2_0 : (twinPrimeSegment 104857645 105906221).card = 4096 := by
  simpa using combineTwinPrimeSegments (by decide : 104857645 ≤ 105381933)
    (by decide : 105381933 ≤ 105906221) join_1_0 join_1_1

theorem join_2_1 : (twinPrimeSegment 105906221 106954797).card = 4107 := by
  simpa using combineTwinPrimeSegments (by decide : 105906221 ≤ 106430509)
    (by decide : 106430509 ≤ 106954797) join_1_2 join_1_3

theorem join_3_0 : (twinPrimeSegment 104857645 106954797).card = 8203 := by
  simpa using combineTwinPrimeSegments (by decide : 104857645 ≤ 105906221)
    (by decide : 105906221 ≤ 106954797) join_2_0 join_2_1

theorem total : (twinPrimeSegment 104857645 106954797).card = 8203 := join_3_0

end S050All
end Sude.GeneratedTwinScan
