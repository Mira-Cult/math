import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S103C12
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14751)) 217579565 217612333 = 120 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 217579565 217612333).card = 120 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14751 217579565 217612333
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14752)) 217612333 217645101 = 94 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 217612333 217645101).card = 94 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14752 217612333 217645101
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14753)) 217645101 217677869 = 99 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 217645101 217677869).card = 99 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14753 217645101 217677869
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14755)) 217677869 217710637 = 123 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 217677869 217710637).card = 123 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14755 217677869 217710637
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 217579565 217645101).card = 214 := by
  simpa using combineTwinPrimeSegments (by decide : 217579565 ≤ 217612333)
    (by decide : 217612333 ≤ 217645101) block0 block1

theorem join_0_1 : (twinPrimeSegment 217645101 217710637).card = 222 := by
  simpa using combineTwinPrimeSegments (by decide : 217645101 ≤ 217677869)
    (by decide : 217677869 ≤ 217710637) block2 block3

theorem join_1_0 : (twinPrimeSegment 217579565 217710637).card = 436 := by
  simpa using combineTwinPrimeSegments (by decide : 217579565 ≤ 217645101)
    (by decide : 217645101 ≤ 217710637) join_0_0 join_0_1

theorem total : (twinPrimeSegment 217579565 217710637).card = 436 := join_1_0

end S103C12
end Sude.GeneratedTwinScan
