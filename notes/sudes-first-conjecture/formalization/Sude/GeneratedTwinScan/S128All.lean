import Sude.GeneratedTwinScan.S128C00
import Sude.GeneratedTwinScan.S128C01
import Sude.GeneratedTwinScan.S128C02
import Sude.GeneratedTwinScan.S128C03
import Sude.GeneratedTwinScan.S128C04
import Sude.GeneratedTwinScan.S128C05
import Sude.GeneratedTwinScan.S128C06
import Sude.GeneratedTwinScan.S128C07
import Sude.GeneratedTwinScan.S128C08
import Sude.GeneratedTwinScan.S128C09
import Sude.GeneratedTwinScan.S128C10
import Sude.GeneratedTwinScan.S128C11
import Sude.GeneratedTwinScan.S128C12
import Sude.GeneratedTwinScan.S128C13
import Sude.GeneratedTwinScan.S128C14
import Sude.GeneratedTwinScan.S128C15

/-! Combined FT source segment; Lean kernel check required. -/
namespace Sude.GeneratedTwinScan
namespace S128All

theorem join_0_0 : (twinPrimeSegment 268435501 268697645).card = 914 := by
  simpa using combineTwinPrimeSegments (by decide : 268435501 ≤ 268566573)
    (by decide : 268566573 ≤ 268697645) S128C00.total S128C01.total

theorem join_0_1 : (twinPrimeSegment 268697645 268959789).card = 906 := by
  simpa using combineTwinPrimeSegments (by decide : 268697645 ≤ 268828717)
    (by decide : 268828717 ≤ 268959789) S128C02.total S128C03.total

theorem join_0_2 : (twinPrimeSegment 268959789 269221933).card = 914 := by
  simpa using combineTwinPrimeSegments (by decide : 268959789 ≤ 269090861)
    (by decide : 269090861 ≤ 269221933) S128C04.total S128C05.total

theorem join_0_3 : (twinPrimeSegment 269221933 269484077).card = 910 := by
  simpa using combineTwinPrimeSegments (by decide : 269221933 ≤ 269353005)
    (by decide : 269353005 ≤ 269484077) S128C06.total S128C07.total

theorem join_0_4 : (twinPrimeSegment 269484077 269746221).card = 933 := by
  simpa using combineTwinPrimeSegments (by decide : 269484077 ≤ 269615149)
    (by decide : 269615149 ≤ 269746221) S128C08.total S128C09.total

theorem join_0_5 : (twinPrimeSegment 269746221 270008365).card = 915 := by
  simpa using combineTwinPrimeSegments (by decide : 269746221 ≤ 269877293)
    (by decide : 269877293 ≤ 270008365) S128C10.total S128C11.total

theorem join_0_6 : (twinPrimeSegment 270008365 270270509).card = 944 := by
  simpa using combineTwinPrimeSegments (by decide : 270008365 ≤ 270139437)
    (by decide : 270139437 ≤ 270270509) S128C12.total S128C13.total

theorem join_0_7 : (twinPrimeSegment 270270509 270532653).card = 921 := by
  simpa using combineTwinPrimeSegments (by decide : 270270509 ≤ 270401581)
    (by decide : 270401581 ≤ 270532653) S128C14.total S128C15.total

theorem join_1_0 : (twinPrimeSegment 268435501 268959789).card = 1820 := by
  simpa using combineTwinPrimeSegments (by decide : 268435501 ≤ 268697645)
    (by decide : 268697645 ≤ 268959789) join_0_0 join_0_1

theorem join_1_1 : (twinPrimeSegment 268959789 269484077).card = 1824 := by
  simpa using combineTwinPrimeSegments (by decide : 268959789 ≤ 269221933)
    (by decide : 269221933 ≤ 269484077) join_0_2 join_0_3

theorem join_1_2 : (twinPrimeSegment 269484077 270008365).card = 1848 := by
  simpa using combineTwinPrimeSegments (by decide : 269484077 ≤ 269746221)
    (by decide : 269746221 ≤ 270008365) join_0_4 join_0_5

theorem join_1_3 : (twinPrimeSegment 270008365 270532653).card = 1865 := by
  simpa using combineTwinPrimeSegments (by decide : 270008365 ≤ 270270509)
    (by decide : 270270509 ≤ 270532653) join_0_6 join_0_7

theorem join_2_0 : (twinPrimeSegment 268435501 269484077).card = 3644 := by
  simpa using combineTwinPrimeSegments (by decide : 268435501 ≤ 268959789)
    (by decide : 268959789 ≤ 269484077) join_1_0 join_1_1

theorem join_2_1 : (twinPrimeSegment 269484077 270532653).card = 3713 := by
  simpa using combineTwinPrimeSegments (by decide : 269484077 ≤ 270008365)
    (by decide : 270008365 ≤ 270532653) join_1_2 join_1_3

theorem join_3_0 : (twinPrimeSegment 268435501 270532653).card = 7357 := by
  simpa using combineTwinPrimeSegments (by decide : 268435501 ≤ 269484077)
    (by decide : 269484077 ≤ 270532653) join_2_0 join_2_1

theorem total : (twinPrimeSegment 268435501 270532653).card = 7357 := join_3_0

end S128All
end Sude.GeneratedTwinScan
