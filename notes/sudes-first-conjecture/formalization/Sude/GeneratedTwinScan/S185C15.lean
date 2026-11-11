import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S185C15
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19747)) 389939245 389972013 = 105 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 389939245 389972013).card = 105 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19747 389939245 389972013
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19748)) 389972013 390004781 = 85 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 389972013 390004781).card = 85 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19748 389972013 390004781
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19749)) 390004781 390037549 = 112 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 390004781 390037549).card = 112 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19749 390004781 390037549
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19750)) 390037549 390070317 = 120 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 390037549 390070317).card = 120 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19750 390037549 390070317
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 389939245 390004781).card = 190 := by
  simpa using combineTwinPrimeSegments (by decide : 389939245 ≤ 389972013)
    (by decide : 389972013 ≤ 390004781) block0 block1

theorem join_0_1 : (twinPrimeSegment 390004781 390070317).card = 232 := by
  simpa using combineTwinPrimeSegments (by decide : 390004781 ≤ 390037549)
    (by decide : 390037549 ≤ 390070317) block2 block3

theorem join_1_0 : (twinPrimeSegment 389939245 390070317).card = 422 := by
  simpa using combineTwinPrimeSegments (by decide : 389939245 ≤ 390004781)
    (by decide : 390004781 ≤ 390070317) join_0_0 join_0_1

theorem total : (twinPrimeSegment 389939245 390070317).card = 422 := join_1_0

end S185C15
end Sude.GeneratedTwinScan
