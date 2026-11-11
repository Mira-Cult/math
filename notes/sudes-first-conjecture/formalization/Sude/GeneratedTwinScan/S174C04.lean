import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S174C04
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19117)) 365428781 365461549 = 106 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 365428781 365461549).card = 106 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19117 365428781 365461549
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19117)) 365461549 365494317 = 108 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 365461549 365494317).card = 108 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19117 365461549 365494317
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19118)) 365494317 365527085 = 123 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 365494317 365527085).card = 123 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19118 365494317 365527085
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19119)) 365527085 365559853 = 120 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 365527085 365559853).card = 120 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19119 365527085 365559853
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 365428781 365494317).card = 214 := by
  simpa using combineTwinPrimeSegments (by decide : 365428781 ≤ 365461549)
    (by decide : 365461549 ≤ 365494317) block0 block1

theorem join_0_1 : (twinPrimeSegment 365494317 365559853).card = 243 := by
  simpa using combineTwinPrimeSegments (by decide : 365494317 ≤ 365527085)
    (by decide : 365527085 ≤ 365559853) block2 block3

theorem join_1_0 : (twinPrimeSegment 365428781 365559853).card = 457 := by
  simpa using combineTwinPrimeSegments (by decide : 365428781 ≤ 365494317)
    (by decide : 365494317 ≤ 365559853) join_0_0 join_0_1

theorem total : (twinPrimeSegment 365428781 365559853).card = 457 := join_1_0

end S174C04
end Sude.GeneratedTwinScan
