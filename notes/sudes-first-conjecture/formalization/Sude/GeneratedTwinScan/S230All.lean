import Sude.GeneratedTwinScan.S230C00
import Sude.GeneratedTwinScan.S230C01
import Sude.GeneratedTwinScan.S230C02
import Sude.GeneratedTwinScan.S230C03
import Sude.GeneratedTwinScan.S230C04
import Sude.GeneratedTwinScan.S230C05
import Sude.GeneratedTwinScan.S230C06
import Sude.GeneratedTwinScan.S230C07
import Sude.GeneratedTwinScan.S230C08
import Sude.GeneratedTwinScan.S230C09
import Sude.GeneratedTwinScan.S230C10
import Sude.GeneratedTwinScan.S230C11
import Sude.GeneratedTwinScan.S230C12
import Sude.GeneratedTwinScan.S230C13
import Sude.GeneratedTwinScan.S230C14
import Sude.GeneratedTwinScan.S230C15

/-! Combined FT source segment; Lean kernel check required. -/
namespace Sude.GeneratedTwinScan
namespace S230All

theorem join_0_0 : (twinPrimeSegment 482345005 482607149).card = 866 := by
  simpa using combineTwinPrimeSegments (by decide : 482345005 ≤ 482476077)
    (by decide : 482476077 ≤ 482607149) S230C00.total S230C01.total

theorem join_0_1 : (twinPrimeSegment 482607149 482869293).card = 833 := by
  simpa using combineTwinPrimeSegments (by decide : 482607149 ≤ 482738221)
    (by decide : 482738221 ≤ 482869293) S230C02.total S230C03.total

theorem join_0_2 : (twinPrimeSegment 482869293 483131437).card = 860 := by
  simpa using combineTwinPrimeSegments (by decide : 482869293 ≤ 483000365)
    (by decide : 483000365 ≤ 483131437) S230C04.total S230C05.total

theorem join_0_3 : (twinPrimeSegment 483131437 483393581).card = 864 := by
  simpa using combineTwinPrimeSegments (by decide : 483131437 ≤ 483262509)
    (by decide : 483262509 ≤ 483393581) S230C06.total S230C07.total

theorem join_0_4 : (twinPrimeSegment 483393581 483655725).card = 891 := by
  simpa using combineTwinPrimeSegments (by decide : 483393581 ≤ 483524653)
    (by decide : 483524653 ≤ 483655725) S230C08.total S230C09.total

theorem join_0_5 : (twinPrimeSegment 483655725 483917869).card = 817 := by
  simpa using combineTwinPrimeSegments (by decide : 483655725 ≤ 483786797)
    (by decide : 483786797 ≤ 483917869) S230C10.total S230C11.total

theorem join_0_6 : (twinPrimeSegment 483917869 484180013).card = 920 := by
  simpa using combineTwinPrimeSegments (by decide : 483917869 ≤ 484048941)
    (by decide : 484048941 ≤ 484180013) S230C12.total S230C13.total

theorem join_0_7 : (twinPrimeSegment 484180013 484442157).card = 859 := by
  simpa using combineTwinPrimeSegments (by decide : 484180013 ≤ 484311085)
    (by decide : 484311085 ≤ 484442157) S230C14.total S230C15.total

theorem join_1_0 : (twinPrimeSegment 482345005 482869293).card = 1699 := by
  simpa using combineTwinPrimeSegments (by decide : 482345005 ≤ 482607149)
    (by decide : 482607149 ≤ 482869293) join_0_0 join_0_1

theorem join_1_1 : (twinPrimeSegment 482869293 483393581).card = 1724 := by
  simpa using combineTwinPrimeSegments (by decide : 482869293 ≤ 483131437)
    (by decide : 483131437 ≤ 483393581) join_0_2 join_0_3

theorem join_1_2 : (twinPrimeSegment 483393581 483917869).card = 1708 := by
  simpa using combineTwinPrimeSegments (by decide : 483393581 ≤ 483655725)
    (by decide : 483655725 ≤ 483917869) join_0_4 join_0_5

theorem join_1_3 : (twinPrimeSegment 483917869 484442157).card = 1779 := by
  simpa using combineTwinPrimeSegments (by decide : 483917869 ≤ 484180013)
    (by decide : 484180013 ≤ 484442157) join_0_6 join_0_7

theorem join_2_0 : (twinPrimeSegment 482345005 483393581).card = 3423 := by
  simpa using combineTwinPrimeSegments (by decide : 482345005 ≤ 482869293)
    (by decide : 482869293 ≤ 483393581) join_1_0 join_1_1

theorem join_2_1 : (twinPrimeSegment 483393581 484442157).card = 3487 := by
  simpa using combineTwinPrimeSegments (by decide : 483393581 ≤ 483917869)
    (by decide : 483917869 ≤ 484442157) join_1_2 join_1_3

theorem join_3_0 : (twinPrimeSegment 482345005 484442157).card = 6910 := by
  simpa using combineTwinPrimeSegments (by decide : 482345005 ≤ 483393581)
    (by decide : 483393581 ≤ 484442157) join_2_0 join_2_1

theorem total : (twinPrimeSegment 482345005 484442157).card = 6910 := join_3_0

end S230All
end Sude.GeneratedTwinScan
