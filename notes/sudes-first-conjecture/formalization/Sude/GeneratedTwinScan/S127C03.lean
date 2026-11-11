import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S127C03
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16332)) 266731565 266764333 = 109 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 266731565 266764333).card = 109 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16332 266731565 266764333
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16333)) 266764333 266797101 = 94 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 266764333 266797101).card = 94 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16333 266764333 266797101
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16334)) 266797101 266829869 = 109 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 266797101 266829869).card = 109 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16334 266797101 266829869
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16335)) 266829869 266862637 = 125 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 266829869 266862637).card = 125 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16335 266829869 266862637
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 266731565 266797101).card = 203 := by
  simpa using combineTwinPrimeSegments (by decide : 266731565 ≤ 266764333)
    (by decide : 266764333 ≤ 266797101) block0 block1

theorem join_0_1 : (twinPrimeSegment 266797101 266862637).card = 234 := by
  simpa using combineTwinPrimeSegments (by decide : 266797101 ≤ 266829869)
    (by decide : 266829869 ≤ 266862637) block2 block3

theorem join_1_0 : (twinPrimeSegment 266731565 266862637).card = 437 := by
  simpa using combineTwinPrimeSegments (by decide : 266731565 ≤ 266797101)
    (by decide : 266797101 ≤ 266862637) join_0_0 join_0_1

theorem total : (twinPrimeSegment 266731565 266862637).card = 437 := join_1_0

end S127C03
end Sude.GeneratedTwinScan
