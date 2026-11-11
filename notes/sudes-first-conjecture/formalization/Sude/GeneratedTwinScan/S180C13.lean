import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S180C13
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19473)) 379191341 379224109 = 96 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 379191341 379224109).card = 96 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19473 379191341 379224109
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19474)) 379224109 379256877 = 117 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 379224109 379256877).card = 117 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19474 379224109 379256877
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19475)) 379256877 379289645 = 106 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 379256877 379289645).card = 106 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19475 379256877 379289645
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19476)) 379289645 379322413 = 114 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 379289645 379322413).card = 114 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19476 379289645 379322413
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 379191341 379256877).card = 213 := by
  simpa using combineTwinPrimeSegments (by decide : 379191341 ≤ 379224109)
    (by decide : 379224109 ≤ 379256877) block0 block1

theorem join_0_1 : (twinPrimeSegment 379256877 379322413).card = 220 := by
  simpa using combineTwinPrimeSegments (by decide : 379256877 ≤ 379289645)
    (by decide : 379289645 ≤ 379322413) block2 block3

theorem join_1_0 : (twinPrimeSegment 379191341 379322413).card = 433 := by
  simpa using combineTwinPrimeSegments (by decide : 379191341 ≤ 379256877)
    (by decide : 379256877 ≤ 379322413) join_0_0 join_0_1

theorem total : (twinPrimeSegment 379191341 379322413).card = 433 := join_1_0

end S180C13
end Sude.GeneratedTwinScan
