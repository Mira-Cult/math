import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S078C04
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 12811)) 164102189 164134957 = 139 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 164102189 164134957).card = 139 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 12811 164102189 164134957
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 12812)) 164134957 164167725 = 137 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 164134957 164167725).card = 137 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 12812 164134957 164167725
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 12814)) 164167725 164200493 = 128 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 164167725 164200493).card = 128 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 12814 164167725 164200493
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 12815)) 164200493 164233261 = 113 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 164200493 164233261).card = 113 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 12815 164200493 164233261
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 164102189 164167725).card = 276 := by
  simpa using combineTwinPrimeSegments (by decide : 164102189 ≤ 164134957)
    (by decide : 164134957 ≤ 164167725) block0 block1

theorem join_0_1 : (twinPrimeSegment 164167725 164233261).card = 241 := by
  simpa using combineTwinPrimeSegments (by decide : 164167725 ≤ 164200493)
    (by decide : 164200493 ≤ 164233261) block2 block3

theorem join_1_0 : (twinPrimeSegment 164102189 164233261).card = 517 := by
  simpa using combineTwinPrimeSegments (by decide : 164102189 ≤ 164167725)
    (by decide : 164167725 ≤ 164233261) join_0_0 join_0_1

theorem total : (twinPrimeSegment 164102189 164233261).card = 517 := join_1_0

end S078C04
end Sude.GeneratedTwinScan
