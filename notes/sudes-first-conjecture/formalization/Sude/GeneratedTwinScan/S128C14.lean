import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S128C14
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16440)) 270270509 270303277 = 117 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 270270509 270303277).card = 117 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16440 270270509 270303277
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16441)) 270303277 270336045 = 118 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 270303277 270336045).card = 118 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16441 270303277 270336045
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16442)) 270336045 270368813 = 100 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 270336045 270368813).card = 100 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16442 270336045 270368813
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16443)) 270368813 270401581 = 107 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 270368813 270401581).card = 107 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16443 270368813 270401581
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 270270509 270336045).card = 235 := by
  simpa using combineTwinPrimeSegments (by decide : 270270509 ≤ 270303277)
    (by decide : 270303277 ≤ 270336045) block0 block1

theorem join_0_1 : (twinPrimeSegment 270336045 270401581).card = 207 := by
  simpa using combineTwinPrimeSegments (by decide : 270336045 ≤ 270368813)
    (by decide : 270368813 ≤ 270401581) block2 block3

theorem join_1_0 : (twinPrimeSegment 270270509 270401581).card = 442 := by
  simpa using combineTwinPrimeSegments (by decide : 270270509 ≤ 270336045)
    (by decide : 270336045 ≤ 270401581) join_0_0 join_0_1

theorem total : (twinPrimeSegment 270270509 270401581).card = 442 := join_1_0

end S128C14
end Sude.GeneratedTwinScan
