import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S210C12
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21023)) 441974829 442007597 = 115 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 441974829 442007597).card = 115 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21023 441974829 442007597
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21024)) 442007597 442040365 = 97 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 442007597 442040365).card = 97 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21024 442007597 442040365
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21025)) 442040365 442073133 = 111 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 442040365 442073133).card = 111 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21025 442040365 442073133
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21026)) 442073133 442105901 = 118 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 442073133 442105901).card = 118 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21026 442073133 442105901
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 441974829 442040365).card = 212 := by
  simpa using combineTwinPrimeSegments (by decide : 441974829 ≤ 442007597)
    (by decide : 442007597 ≤ 442040365) block0 block1

theorem join_0_1 : (twinPrimeSegment 442040365 442105901).card = 229 := by
  simpa using combineTwinPrimeSegments (by decide : 442040365 ≤ 442073133)
    (by decide : 442073133 ≤ 442105901) block2 block3

theorem join_1_0 : (twinPrimeSegment 441974829 442105901).card = 441 := by
  simpa using combineTwinPrimeSegments (by decide : 441974829 ≤ 442040365)
    (by decide : 442040365 ≤ 442105901) join_0_0 join_0_1

theorem total : (twinPrimeSegment 441974829 442105901).card = 441 := join_1_0

end S210C12
end Sude.GeneratedTwinScan
