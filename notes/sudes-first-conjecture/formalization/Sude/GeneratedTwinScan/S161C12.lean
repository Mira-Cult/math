import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S161C12
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18418)) 339214381 339247149 = 92 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 339214381 339247149).card = 92 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18418 339214381 339247149
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18419)) 339247149 339279917 = 112 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 339247149 339279917).card = 112 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18419 339247149 339279917
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18420)) 339279917 339312685 = 110 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 339279917 339312685).card = 110 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18420 339279917 339312685
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18421)) 339312685 339345453 = 128 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 339312685 339345453).card = 128 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18421 339312685 339345453
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 339214381 339279917).card = 204 := by
  simpa using combineTwinPrimeSegments (by decide : 339214381 ≤ 339247149)
    (by decide : 339247149 ≤ 339279917) block0 block1

theorem join_0_1 : (twinPrimeSegment 339279917 339345453).card = 238 := by
  simpa using combineTwinPrimeSegments (by decide : 339279917 ≤ 339312685)
    (by decide : 339312685 ≤ 339345453) block2 block3

theorem join_1_0 : (twinPrimeSegment 339214381 339345453).card = 442 := by
  simpa using combineTwinPrimeSegments (by decide : 339214381 ≤ 339279917)
    (by decide : 339279917 ≤ 339345453) join_0_0 join_0_1

theorem total : (twinPrimeSegment 339214381 339345453).card = 442 := join_1_0

end S161C12
end Sude.GeneratedTwinScan
