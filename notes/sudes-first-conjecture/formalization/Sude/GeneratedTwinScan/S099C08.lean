import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S099C08
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14446)) 208666669 208699437 = 107 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 208666669 208699437).card = 107 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14446 208666669 208699437
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14447)) 208699437 208732205 = 117 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 208699437 208732205).card = 117 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14447 208699437 208732205
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14448)) 208732205 208764973 = 126 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 208732205 208764973).card = 126 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14448 208732205 208764973
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14449)) 208764973 208797741 = 116 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 208764973 208797741).card = 116 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14449 208764973 208797741
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 208666669 208732205).card = 224 := by
  simpa using combineTwinPrimeSegments (by decide : 208666669 ≤ 208699437)
    (by decide : 208699437 ≤ 208732205) block0 block1

theorem join_0_1 : (twinPrimeSegment 208732205 208797741).card = 242 := by
  simpa using combineTwinPrimeSegments (by decide : 208732205 ≤ 208764973)
    (by decide : 208764973 ≤ 208797741) block2 block3

theorem join_1_0 : (twinPrimeSegment 208666669 208797741).card = 466 := by
  simpa using combineTwinPrimeSegments (by decide : 208666669 ≤ 208732205)
    (by decide : 208732205 ≤ 208797741) join_0_0 join_0_1

theorem total : (twinPrimeSegment 208666669 208797741).card = 466 := join_1_0

end S099C08
end Sude.GeneratedTwinScan
