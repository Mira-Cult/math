import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S096C09
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14231)) 202506285 202539053 = 114 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 202506285 202539053).card = 114 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14231 202506285 202539053
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14232)) 202539053 202571821 = 106 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 202539053 202571821).card = 106 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14232 202539053 202571821
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14233)) 202571821 202604589 = 121 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 202571821 202604589).card = 121 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14233 202571821 202604589
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14235)) 202604589 202637357 = 107 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 202604589 202637357).card = 107 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14235 202604589 202637357
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 202506285 202571821).card = 220 := by
  simpa using combineTwinPrimeSegments (by decide : 202506285 ≤ 202539053)
    (by decide : 202539053 ≤ 202571821) block0 block1

theorem join_0_1 : (twinPrimeSegment 202571821 202637357).card = 228 := by
  simpa using combineTwinPrimeSegments (by decide : 202571821 ≤ 202604589)
    (by decide : 202604589 ≤ 202637357) block2 block3

theorem join_1_0 : (twinPrimeSegment 202506285 202637357).card = 448 := by
  simpa using combineTwinPrimeSegments (by decide : 202506285 ≤ 202571821)
    (by decide : 202571821 ≤ 202637357) join_0_0 join_0_1

theorem total : (twinPrimeSegment 202506285 202637357).card = 448 := join_1_0

end S096C09
end Sude.GeneratedTwinScan
