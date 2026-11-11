import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S074C14
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 12532)) 157024301 157057069 = 119 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 157024301 157057069).card = 119 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 12532 157024301 157057069
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 12533)) 157057069 157089837 = 130 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 157057069 157089837).card = 130 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 12533 157057069 157089837
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 12534)) 157089837 157122605 = 119 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 157089837 157122605).card = 119 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 12534 157089837 157122605
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 12536)) 157122605 157155373 = 124 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 157122605 157155373).card = 124 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 12536 157122605 157155373
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 157024301 157089837).card = 249 := by
  simpa using combineTwinPrimeSegments (by decide : 157024301 ≤ 157057069)
    (by decide : 157057069 ≤ 157089837) block0 block1

theorem join_0_1 : (twinPrimeSegment 157089837 157155373).card = 243 := by
  simpa using combineTwinPrimeSegments (by decide : 157089837 ≤ 157122605)
    (by decide : 157122605 ≤ 157155373) block2 block3

theorem join_1_0 : (twinPrimeSegment 157024301 157155373).card = 492 := by
  simpa using combineTwinPrimeSegments (by decide : 157024301 ≤ 157089837)
    (by decide : 157089837 ≤ 157155373) join_0_0 join_0_1

theorem total : (twinPrimeSegment 157024301 157155373).card = 492 := join_1_0

end S074C14
end Sude.GeneratedTwinScan
