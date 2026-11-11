import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S188C01
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19860)) 394395693 394428461 = 91 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 394395693 394428461).card = 91 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19860 394395693 394428461
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19861)) 394428461 394461229 = 111 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 394428461 394461229).card = 111 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19861 394428461 394461229
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19861)) 394461229 394493997 = 111 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 394461229 394493997).card = 111 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19861 394461229 394493997
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19862)) 394493997 394526765 = 118 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 394493997 394526765).card = 118 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19862 394493997 394526765
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 394395693 394461229).card = 202 := by
  simpa using combineTwinPrimeSegments (by decide : 394395693 ≤ 394428461)
    (by decide : 394428461 ≤ 394461229) block0 block1

theorem join_0_1 : (twinPrimeSegment 394461229 394526765).card = 229 := by
  simpa using combineTwinPrimeSegments (by decide : 394461229 ≤ 394493997)
    (by decide : 394493997 ≤ 394526765) block2 block3

theorem join_1_0 : (twinPrimeSegment 394395693 394526765).card = 431 := by
  simpa using combineTwinPrimeSegments (by decide : 394395693 ≤ 394461229)
    (by decide : 394461229 ≤ 394526765) join_0_0 join_0_1

theorem total : (twinPrimeSegment 394395693 394526765).card = 431 := join_1_0

end S188C01
end Sude.GeneratedTwinScan
