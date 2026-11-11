import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S227C07
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21840)) 476971053 477003821 = 121 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 476971053 477003821).card = 121 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21840 476971053 477003821
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21841)) 477003821 477036589 = 107 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 477003821 477036589).card = 107 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21841 477003821 477036589
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21841)) 477036589 477069357 = 97 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 477036589 477069357).card = 97 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21841 477036589 477069357
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21842)) 477069357 477102125 = 105 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 477069357 477102125).card = 105 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21842 477069357 477102125
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 476971053 477036589).card = 228 := by
  simpa using combineTwinPrimeSegments (by decide : 476971053 ≤ 477003821)
    (by decide : 477003821 ≤ 477036589) block0 block1

theorem join_0_1 : (twinPrimeSegment 477036589 477102125).card = 202 := by
  simpa using combineTwinPrimeSegments (by decide : 477036589 ≤ 477069357)
    (by decide : 477069357 ≤ 477102125) block2 block3

theorem join_1_0 : (twinPrimeSegment 476971053 477102125).card = 430 := by
  simpa using combineTwinPrimeSegments (by decide : 476971053 ≤ 477036589)
    (by decide : 477036589 ≤ 477102125) join_0_0 join_0_1

theorem total : (twinPrimeSegment 476971053 477102125).card = 430 := join_1_0

end S227C07
end Sude.GeneratedTwinScan
