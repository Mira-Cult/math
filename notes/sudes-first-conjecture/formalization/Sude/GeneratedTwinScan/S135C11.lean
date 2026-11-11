import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S135C11
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16869)) 284557357 284590125 = 116 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 284557357 284590125).card = 116 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16869 284557357 284590125
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16870)) 284590125 284622893 = 122 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 284590125 284622893).card = 122 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16870 284590125 284622893
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16871)) 284622893 284655661 = 111 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 284622893 284655661).card = 111 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16871 284622893 284655661
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16872)) 284655661 284688429 = 127 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 284655661 284688429).card = 127 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16872 284655661 284688429
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 284557357 284622893).card = 238 := by
  simpa using combineTwinPrimeSegments (by decide : 284557357 ≤ 284590125)
    (by decide : 284590125 ≤ 284622893) block0 block1

theorem join_0_1 : (twinPrimeSegment 284622893 284688429).card = 238 := by
  simpa using combineTwinPrimeSegments (by decide : 284622893 ≤ 284655661)
    (by decide : 284655661 ≤ 284688429) block2 block3

theorem join_1_0 : (twinPrimeSegment 284557357 284688429).card = 476 := by
  simpa using combineTwinPrimeSegments (by decide : 284557357 ≤ 284622893)
    (by decide : 284622893 ≤ 284688429) join_0_0 join_0_1

theorem total : (twinPrimeSegment 284557357 284688429).card = 476 := join_1_0

end S135C11
end Sude.GeneratedTwinScan
