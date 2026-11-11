import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S087C12
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13566)) 184025133 184057901 = 116 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 184025133 184057901).card = 116 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13566 184025133 184057901
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13568)) 184057901 184090669 = 108 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 184057901 184090669).card = 108 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13568 184057901 184090669
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13569)) 184090669 184123437 = 107 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 184090669 184123437).card = 107 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13569 184090669 184123437
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13570)) 184123437 184156205 = 122 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 184123437 184156205).card = 122 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13570 184123437 184156205
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 184025133 184090669).card = 224 := by
  simpa using combineTwinPrimeSegments (by decide : 184025133 ≤ 184057901)
    (by decide : 184057901 ≤ 184090669) block0 block1

theorem join_0_1 : (twinPrimeSegment 184090669 184156205).card = 229 := by
  simpa using combineTwinPrimeSegments (by decide : 184090669 ≤ 184123437)
    (by decide : 184123437 ≤ 184156205) block2 block3

theorem join_1_0 : (twinPrimeSegment 184025133 184156205).card = 453 := by
  simpa using combineTwinPrimeSegments (by decide : 184025133 ≤ 184090669)
    (by decide : 184090669 ≤ 184156205) join_0_0 join_0_1

theorem total : (twinPrimeSegment 184025133 184156205).card = 453 := join_1_0

end S087C12
end Sude.GeneratedTwinScan
