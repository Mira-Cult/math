import Sude.GeneratedTwinScan.S211C00
import Sude.GeneratedTwinScan.S211C01
import Sude.GeneratedTwinScan.S211C02
import Sude.GeneratedTwinScan.S211C03
import Sude.GeneratedTwinScan.S211C04
import Sude.GeneratedTwinScan.S211C05
import Sude.GeneratedTwinScan.S211C06
import Sude.GeneratedTwinScan.S211C07
import Sude.GeneratedTwinScan.S211C08
import Sude.GeneratedTwinScan.S211C09
import Sude.GeneratedTwinScan.S211C10
import Sude.GeneratedTwinScan.S211C11
import Sude.GeneratedTwinScan.S211C12
import Sude.GeneratedTwinScan.S211C13
import Sude.GeneratedTwinScan.S211C14
import Sude.GeneratedTwinScan.S211C15

/-! Combined FT source segment; Lean kernel check required. -/
namespace Sude.GeneratedTwinScan
namespace S211All

theorem join_0_0 : (twinPrimeSegment 442499117 442761261).card = 867 := by
  simpa using combineTwinPrimeSegments (by decide : 442499117 ≤ 442630189)
    (by decide : 442630189 ≤ 442761261) S211C00.total S211C01.total

theorem join_0_1 : (twinPrimeSegment 442761261 443023405).card = 885 := by
  simpa using combineTwinPrimeSegments (by decide : 442761261 ≤ 442892333)
    (by decide : 442892333 ≤ 443023405) S211C02.total S211C03.total

theorem join_0_2 : (twinPrimeSegment 443023405 443285549).card = 847 := by
  simpa using combineTwinPrimeSegments (by decide : 443023405 ≤ 443154477)
    (by decide : 443154477 ≤ 443285549) S211C04.total S211C05.total

theorem join_0_3 : (twinPrimeSegment 443285549 443547693).card = 905 := by
  simpa using combineTwinPrimeSegments (by decide : 443285549 ≤ 443416621)
    (by decide : 443416621 ≤ 443547693) S211C06.total S211C07.total

theorem join_0_4 : (twinPrimeSegment 443547693 443809837).card = 901 := by
  simpa using combineTwinPrimeSegments (by decide : 443547693 ≤ 443678765)
    (by decide : 443678765 ≤ 443809837) S211C08.total S211C09.total

theorem join_0_5 : (twinPrimeSegment 443809837 444071981).card = 875 := by
  simpa using combineTwinPrimeSegments (by decide : 443809837 ≤ 443940909)
    (by decide : 443940909 ≤ 444071981) S211C10.total S211C11.total

theorem join_0_6 : (twinPrimeSegment 444071981 444334125).card = 852 := by
  simpa using combineTwinPrimeSegments (by decide : 444071981 ≤ 444203053)
    (by decide : 444203053 ≤ 444334125) S211C12.total S211C13.total

theorem join_0_7 : (twinPrimeSegment 444334125 444596269).card = 851 := by
  simpa using combineTwinPrimeSegments (by decide : 444334125 ≤ 444465197)
    (by decide : 444465197 ≤ 444596269) S211C14.total S211C15.total

theorem join_1_0 : (twinPrimeSegment 442499117 443023405).card = 1752 := by
  simpa using combineTwinPrimeSegments (by decide : 442499117 ≤ 442761261)
    (by decide : 442761261 ≤ 443023405) join_0_0 join_0_1

theorem join_1_1 : (twinPrimeSegment 443023405 443547693).card = 1752 := by
  simpa using combineTwinPrimeSegments (by decide : 443023405 ≤ 443285549)
    (by decide : 443285549 ≤ 443547693) join_0_2 join_0_3

theorem join_1_2 : (twinPrimeSegment 443547693 444071981).card = 1776 := by
  simpa using combineTwinPrimeSegments (by decide : 443547693 ≤ 443809837)
    (by decide : 443809837 ≤ 444071981) join_0_4 join_0_5

theorem join_1_3 : (twinPrimeSegment 444071981 444596269).card = 1703 := by
  simpa using combineTwinPrimeSegments (by decide : 444071981 ≤ 444334125)
    (by decide : 444334125 ≤ 444596269) join_0_6 join_0_7

theorem join_2_0 : (twinPrimeSegment 442499117 443547693).card = 3504 := by
  simpa using combineTwinPrimeSegments (by decide : 442499117 ≤ 443023405)
    (by decide : 443023405 ≤ 443547693) join_1_0 join_1_1

theorem join_2_1 : (twinPrimeSegment 443547693 444596269).card = 3479 := by
  simpa using combineTwinPrimeSegments (by decide : 443547693 ≤ 444071981)
    (by decide : 444071981 ≤ 444596269) join_1_2 join_1_3

theorem join_3_0 : (twinPrimeSegment 442499117 444596269).card = 6983 := by
  simpa using combineTwinPrimeSegments (by decide : 442499117 ≤ 443547693)
    (by decide : 443547693 ≤ 444596269) join_2_0 join_2_1

theorem total : (twinPrimeSegment 442499117 444596269).card = 6983 := join_3_0

end S211All
end Sude.GeneratedTwinScan
