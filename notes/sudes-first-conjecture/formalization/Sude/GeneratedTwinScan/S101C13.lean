import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S101C13
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14613)) 213516333 213549101 = 100 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 213516333 213549101).card = 100 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14613 213516333 213549101
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14614)) 213549101 213581869 = 129 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 213549101 213581869).card = 129 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14614 213549101 213581869
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14615)) 213581869 213614637 = 116 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 213581869 213614637).card = 116 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14615 213581869 213614637
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14616)) 213614637 213647405 = 128 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 213614637 213647405).card = 128 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14616 213614637 213647405
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 213516333 213581869).card = 229 := by
  simpa using combineTwinPrimeSegments (by decide : 213516333 ≤ 213549101)
    (by decide : 213549101 ≤ 213581869) block0 block1

theorem join_0_1 : (twinPrimeSegment 213581869 213647405).card = 244 := by
  simpa using combineTwinPrimeSegments (by decide : 213581869 ≤ 213614637)
    (by decide : 213614637 ≤ 213647405) block2 block3

theorem join_1_0 : (twinPrimeSegment 213516333 213647405).card = 473 := by
  simpa using combineTwinPrimeSegments (by decide : 213516333 ≤ 213581869)
    (by decide : 213581869 ≤ 213647405) join_0_0 join_0_1

theorem total : (twinPrimeSegment 213516333 213647405).card = 473 := join_1_0

end S101C13
end Sude.GeneratedTwinScan
