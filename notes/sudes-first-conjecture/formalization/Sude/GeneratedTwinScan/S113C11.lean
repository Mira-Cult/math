import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S113C11
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15441)) 238420013 238452781 = 108 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 238420013 238452781).card = 108 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15441 238420013 238452781
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15442)) 238452781 238485549 = 94 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 238452781 238485549).card = 94 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15442 238452781 238485549
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15444)) 238485549 238518317 = 102 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 238485549 238518317).card = 102 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15444 238485549 238518317
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15445)) 238518317 238551085 = 117 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 238518317 238551085).card = 117 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15445 238518317 238551085
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 238420013 238485549).card = 202 := by
  simpa using combineTwinPrimeSegments (by decide : 238420013 ≤ 238452781)
    (by decide : 238452781 ≤ 238485549) block0 block1

theorem join_0_1 : (twinPrimeSegment 238485549 238551085).card = 219 := by
  simpa using combineTwinPrimeSegments (by decide : 238485549 ≤ 238518317)
    (by decide : 238518317 ≤ 238551085) block2 block3

theorem join_1_0 : (twinPrimeSegment 238420013 238551085).card = 421 := by
  simpa using combineTwinPrimeSegments (by decide : 238420013 ≤ 238485549)
    (by decide : 238485549 ≤ 238551085) join_0_0 join_0_1

theorem total : (twinPrimeSegment 238420013 238551085).card = 421 := join_1_0

end S113C11
end Sude.GeneratedTwinScan
