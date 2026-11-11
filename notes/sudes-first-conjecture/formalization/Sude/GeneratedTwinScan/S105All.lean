import Sude.GeneratedTwinScan.S105C00
import Sude.GeneratedTwinScan.S105C01
import Sude.GeneratedTwinScan.S105C02
import Sude.GeneratedTwinScan.S105C03
import Sude.GeneratedTwinScan.S105C04
import Sude.GeneratedTwinScan.S105C05
import Sude.GeneratedTwinScan.S105C06
import Sude.GeneratedTwinScan.S105C07
import Sude.GeneratedTwinScan.S105C08
import Sude.GeneratedTwinScan.S105C09
import Sude.GeneratedTwinScan.S105C10
import Sude.GeneratedTwinScan.S105C11
import Sude.GeneratedTwinScan.S105C12
import Sude.GeneratedTwinScan.S105C13
import Sude.GeneratedTwinScan.S105C14
import Sude.GeneratedTwinScan.S105C15

/-! Combined FT source segment; Lean kernel check required. -/
namespace Sude.GeneratedTwinScan
namespace S105All

theorem join_0_0 : (twinPrimeSegment 220201005 220463149).card = 966 := by
  simpa using combineTwinPrimeSegments (by decide : 220201005 ≤ 220332077)
    (by decide : 220332077 ≤ 220463149) S105C00.total S105C01.total

theorem join_0_1 : (twinPrimeSegment 220463149 220725293).card = 918 := by
  simpa using combineTwinPrimeSegments (by decide : 220463149 ≤ 220594221)
    (by decide : 220594221 ≤ 220725293) S105C02.total S105C03.total

theorem join_0_2 : (twinPrimeSegment 220725293 220987437).card = 911 := by
  simpa using combineTwinPrimeSegments (by decide : 220725293 ≤ 220856365)
    (by decide : 220856365 ≤ 220987437) S105C04.total S105C05.total

theorem join_0_3 : (twinPrimeSegment 220987437 221249581).card = 940 := by
  simpa using combineTwinPrimeSegments (by decide : 220987437 ≤ 221118509)
    (by decide : 221118509 ≤ 221249581) S105C06.total S105C07.total

theorem join_0_4 : (twinPrimeSegment 221249581 221511725).card = 972 := by
  simpa using combineTwinPrimeSegments (by decide : 221249581 ≤ 221380653)
    (by decide : 221380653 ≤ 221511725) S105C08.total S105C09.total

theorem join_0_5 : (twinPrimeSegment 221511725 221773869).card = 936 := by
  simpa using combineTwinPrimeSegments (by decide : 221511725 ≤ 221642797)
    (by decide : 221642797 ≤ 221773869) S105C10.total S105C11.total

theorem join_0_6 : (twinPrimeSegment 221773869 222036013).card = 947 := by
  simpa using combineTwinPrimeSegments (by decide : 221773869 ≤ 221904941)
    (by decide : 221904941 ≤ 222036013) S105C12.total S105C13.total

theorem join_0_7 : (twinPrimeSegment 222036013 222298157).card = 940 := by
  simpa using combineTwinPrimeSegments (by decide : 222036013 ≤ 222167085)
    (by decide : 222167085 ≤ 222298157) S105C14.total S105C15.total

theorem join_1_0 : (twinPrimeSegment 220201005 220725293).card = 1884 := by
  simpa using combineTwinPrimeSegments (by decide : 220201005 ≤ 220463149)
    (by decide : 220463149 ≤ 220725293) join_0_0 join_0_1

theorem join_1_1 : (twinPrimeSegment 220725293 221249581).card = 1851 := by
  simpa using combineTwinPrimeSegments (by decide : 220725293 ≤ 220987437)
    (by decide : 220987437 ≤ 221249581) join_0_2 join_0_3

theorem join_1_2 : (twinPrimeSegment 221249581 221773869).card = 1908 := by
  simpa using combineTwinPrimeSegments (by decide : 221249581 ≤ 221511725)
    (by decide : 221511725 ≤ 221773869) join_0_4 join_0_5

theorem join_1_3 : (twinPrimeSegment 221773869 222298157).card = 1887 := by
  simpa using combineTwinPrimeSegments (by decide : 221773869 ≤ 222036013)
    (by decide : 222036013 ≤ 222298157) join_0_6 join_0_7

theorem join_2_0 : (twinPrimeSegment 220201005 221249581).card = 3735 := by
  simpa using combineTwinPrimeSegments (by decide : 220201005 ≤ 220725293)
    (by decide : 220725293 ≤ 221249581) join_1_0 join_1_1

theorem join_2_1 : (twinPrimeSegment 221249581 222298157).card = 3795 := by
  simpa using combineTwinPrimeSegments (by decide : 221249581 ≤ 221773869)
    (by decide : 221773869 ≤ 222298157) join_1_2 join_1_3

theorem join_3_0 : (twinPrimeSegment 220201005 222298157).card = 7530 := by
  simpa using combineTwinPrimeSegments (by decide : 220201005 ≤ 221249581)
    (by decide : 221249581 ≤ 222298157) join_2_0 join_2_1

theorem total : (twinPrimeSegment 220201005 222298157).card = 7530 := join_3_0

end S105All
end Sude.GeneratedTwinScan
