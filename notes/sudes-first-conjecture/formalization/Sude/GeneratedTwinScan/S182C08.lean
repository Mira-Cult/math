import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S182C08
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19564)) 382730285 382763053 = 117 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 382730285 382763053).card = 117 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19564 382730285 382763053
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19565)) 382763053 382795821 = 117 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 382763053 382795821).card = 117 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19565 382763053 382795821
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19566)) 382795821 382828589 = 103 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 382795821 382828589).card = 103 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19566 382795821 382828589
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19566)) 382828589 382861357 = 107 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 382828589 382861357).card = 107 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19566 382828589 382861357
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 382730285 382795821).card = 234 := by
  simpa using combineTwinPrimeSegments (by decide : 382730285 ≤ 382763053)
    (by decide : 382763053 ≤ 382795821) block0 block1

theorem join_0_1 : (twinPrimeSegment 382795821 382861357).card = 210 := by
  simpa using combineTwinPrimeSegments (by decide : 382795821 ≤ 382828589)
    (by decide : 382828589 ≤ 382861357) block2 block3

theorem join_1_0 : (twinPrimeSegment 382730285 382861357).card = 444 := by
  simpa using combineTwinPrimeSegments (by decide : 382730285 ≤ 382795821)
    (by decide : 382795821 ≤ 382861357) join_0_0 join_0_1

theorem total : (twinPrimeSegment 382730285 382861357).card = 444 := join_1_0

end S182C08
end Sude.GeneratedTwinScan
