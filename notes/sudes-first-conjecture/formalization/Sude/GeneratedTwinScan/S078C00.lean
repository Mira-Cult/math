import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S078C00
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 12791)) 163577901 163610669 = 126 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 163577901 163610669).card = 126 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 12791 163577901 163610669
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 12792)) 163610669 163643437 = 139 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 163610669 163643437).card = 139 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 12792 163610669 163643437
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 12793)) 163643437 163676205 = 115 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 163643437 163676205).card = 115 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 12793 163643437 163676205
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 12794)) 163676205 163708973 = 113 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 163676205 163708973).card = 113 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 12794 163676205 163708973
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 163577901 163643437).card = 265 := by
  simpa using combineTwinPrimeSegments (by decide : 163577901 ≤ 163610669)
    (by decide : 163610669 ≤ 163643437) block0 block1

theorem join_0_1 : (twinPrimeSegment 163643437 163708973).card = 228 := by
  simpa using combineTwinPrimeSegments (by decide : 163643437 ≤ 163676205)
    (by decide : 163676205 ≤ 163708973) block2 block3

theorem join_1_0 : (twinPrimeSegment 163577901 163708973).card = 493 := by
  simpa using combineTwinPrimeSegments (by decide : 163577901 ≤ 163643437)
    (by decide : 163643437 ≤ 163708973) join_0_0 join_0_1

theorem total : (twinPrimeSegment 163577901 163708973).card = 493 := join_1_0

end S078C00
end Sude.GeneratedTwinScan
