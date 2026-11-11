import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S217C04
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21345)) 455606317 455639085 = 105 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 455606317 455639085).card = 105 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21345 455606317 455639085
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21346)) 455639085 455671853 = 113 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 455639085 455671853).card = 113 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21346 455639085 455671853
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21347)) 455671853 455704621 = 97 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 455671853 455704621).card = 97 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21347 455671853 455704621
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21348)) 455704621 455737389 = 124 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 455704621 455737389).card = 124 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21348 455704621 455737389
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 455606317 455671853).card = 218 := by
  simpa using combineTwinPrimeSegments (by decide : 455606317 ≤ 455639085)
    (by decide : 455639085 ≤ 455671853) block0 block1

theorem join_0_1 : (twinPrimeSegment 455671853 455737389).card = 221 := by
  simpa using combineTwinPrimeSegments (by decide : 455671853 ≤ 455704621)
    (by decide : 455704621 ≤ 455737389) block2 block3

theorem join_1_0 : (twinPrimeSegment 455606317 455737389).card = 439 := by
  simpa using combineTwinPrimeSegments (by decide : 455606317 ≤ 455671853)
    (by decide : 455671853 ≤ 455737389) join_0_0 join_0_1

theorem total : (twinPrimeSegment 455606317 455737389).card = 439 := join_1_0

end S217C04
end Sude.GeneratedTwinScan
