import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S246C08
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22737)) 516948013 516980781 = 99 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 516948013 516980781).card = 99 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22737 516948013 516980781
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22737)) 516980781 517013549 = 102 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 516980781 517013549).card = 102 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22737 516980781 517013549
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22738)) 517013549 517046317 = 105 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 517013549 517046317).card = 105 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22738 517013549 517046317
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22739)) 517046317 517079085 = 101 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 517046317 517079085).card = 101 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22739 517046317 517079085
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 516948013 517013549).card = 201 := by
  simpa using combineTwinPrimeSegments (by decide : 516948013 ≤ 516980781)
    (by decide : 516980781 ≤ 517013549) block0 block1

theorem join_0_1 : (twinPrimeSegment 517013549 517079085).card = 206 := by
  simpa using combineTwinPrimeSegments (by decide : 517013549 ≤ 517046317)
    (by decide : 517046317 ≤ 517079085) block2 block3

theorem join_1_0 : (twinPrimeSegment 516948013 517079085).card = 407 := by
  simpa using combineTwinPrimeSegments (by decide : 516948013 ≤ 517013549)
    (by decide : 517013549 ≤ 517079085) join_0_0 join_0_1

theorem total : (twinPrimeSegment 516948013 517079085).card = 407 := join_1_0

end S246C08
end Sude.GeneratedTwinScan
