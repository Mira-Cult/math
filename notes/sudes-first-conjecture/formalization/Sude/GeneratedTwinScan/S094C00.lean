import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S094C00
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14041)) 197132333 197165101 = 113 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 197132333 197165101).card = 113 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14041 197132333 197165101
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14042)) 197165101 197197869 = 128 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 197165101 197197869).card = 128 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14042 197165101 197197869
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14043)) 197197869 197230637 = 124 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 197197869 197230637).card = 124 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14043 197197869 197230637
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14045)) 197230637 197263405 = 127 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 197230637 197263405).card = 127 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14045 197230637 197263405
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 197132333 197197869).card = 241 := by
  simpa using combineTwinPrimeSegments (by decide : 197132333 ≤ 197165101)
    (by decide : 197165101 ≤ 197197869) block0 block1

theorem join_0_1 : (twinPrimeSegment 197197869 197263405).card = 251 := by
  simpa using combineTwinPrimeSegments (by decide : 197197869 ≤ 197230637)
    (by decide : 197230637 ≤ 197263405) block2 block3

theorem join_1_0 : (twinPrimeSegment 197132333 197263405).card = 492 := by
  simpa using combineTwinPrimeSegments (by decide : 197132333 ≤ 197197869)
    (by decide : 197197869 ≤ 197263405) join_0_0 join_0_1

theorem total : (twinPrimeSegment 197132333 197263405).card = 492 := join_1_0

end S094C00
end Sude.GeneratedTwinScan
