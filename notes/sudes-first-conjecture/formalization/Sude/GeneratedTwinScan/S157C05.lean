import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S157C05
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18164)) 329908269 329941037 = 109 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 329908269 329941037).card = 109 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18164 329908269 329941037
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18165)) 329941037 329973805 = 95 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 329941037 329973805).card = 95 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18165 329941037 329973805
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18166)) 329973805 330006573 = 112 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 329973805 330006573).card = 112 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18166 329973805 330006573
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18166)) 330006573 330039341 = 113 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 330006573 330039341).card = 113 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18166 330006573 330039341
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 329908269 329973805).card = 204 := by
  simpa using combineTwinPrimeSegments (by decide : 329908269 ≤ 329941037)
    (by decide : 329941037 ≤ 329973805) block0 block1

theorem join_0_1 : (twinPrimeSegment 329973805 330039341).card = 225 := by
  simpa using combineTwinPrimeSegments (by decide : 329973805 ≤ 330006573)
    (by decide : 330006573 ≤ 330039341) block2 block3

theorem join_1_0 : (twinPrimeSegment 329908269 330039341).card = 429 := by
  simpa using combineTwinPrimeSegments (by decide : 329908269 ≤ 329973805)
    (by decide : 329973805 ≤ 330039341) join_0_0 join_0_1

theorem total : (twinPrimeSegment 329908269 330039341).card = 429 := join_1_0

end S157C05
end Sude.GeneratedTwinScan
