import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S201C07
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20554)) 422445101 422477869 = 112 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 422445101 422477869).card = 112 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20554 422445101 422477869
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20555)) 422477869 422510637 = 127 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 422477869 422510637).card = 127 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20555 422477869 422510637
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20555)) 422510637 422543405 = 95 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 422510637 422543405).card = 95 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20555 422510637 422543405
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20556)) 422543405 422576173 = 101 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 422543405 422576173).card = 101 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20556 422543405 422576173
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 422445101 422510637).card = 239 := by
  simpa using combineTwinPrimeSegments (by decide : 422445101 ≤ 422477869)
    (by decide : 422477869 ≤ 422510637) block0 block1

theorem join_0_1 : (twinPrimeSegment 422510637 422576173).card = 196 := by
  simpa using combineTwinPrimeSegments (by decide : 422510637 ≤ 422543405)
    (by decide : 422543405 ≤ 422576173) block2 block3

theorem join_1_0 : (twinPrimeSegment 422445101 422576173).card = 435 := by
  simpa using combineTwinPrimeSegments (by decide : 422445101 ≤ 422510637)
    (by decide : 422510637 ≤ 422576173) join_0_0 join_0_1

theorem total : (twinPrimeSegment 422445101 422576173).card = 435 := join_1_0

end S201C07
end Sude.GeneratedTwinScan
