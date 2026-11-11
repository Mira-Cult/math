import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S111C09
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15296)) 233963565 233996333 = 112 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 233963565 233996333).card = 112 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15296 233963565 233996333
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15298)) 233996333 234029101 = 121 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 233996333 234029101).card = 121 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15298 233996333 234029101
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15299)) 234029101 234061869 = 111 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 234029101 234061869).card = 111 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15299 234029101 234061869
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15300)) 234061869 234094637 = 107 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 234061869 234094637).card = 107 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15300 234061869 234094637
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 233963565 234029101).card = 233 := by
  simpa using combineTwinPrimeSegments (by decide : 233963565 ≤ 233996333)
    (by decide : 233996333 ≤ 234029101) block0 block1

theorem join_0_1 : (twinPrimeSegment 234029101 234094637).card = 218 := by
  simpa using combineTwinPrimeSegments (by decide : 234029101 ≤ 234061869)
    (by decide : 234061869 ≤ 234094637) block2 block3

theorem join_1_0 : (twinPrimeSegment 233963565 234094637).card = 451 := by
  simpa using combineTwinPrimeSegments (by decide : 233963565 ≤ 234029101)
    (by decide : 234029101 ≤ 234094637) join_0_0 join_0_1

theorem total : (twinPrimeSegment 233963565 234094637).card = 451 := join_1_0

end S111C09
end Sude.GeneratedTwinScan
