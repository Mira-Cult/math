import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S142C06
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17280)) 298582061 298614829 = 113 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 298582061 298614829).card = 113 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17280 298582061 298614829
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17281)) 298614829 298647597 = 114 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 298614829 298647597).card = 114 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17281 298614829 298647597
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17282)) 298647597 298680365 = 91 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 298647597 298680365).card = 91 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17282 298647597 298680365
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17283)) 298680365 298713133 = 122 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 298680365 298713133).card = 122 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17283 298680365 298713133
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 298582061 298647597).card = 227 := by
  simpa using combineTwinPrimeSegments (by decide : 298582061 ≤ 298614829)
    (by decide : 298614829 ≤ 298647597) block0 block1

theorem join_0_1 : (twinPrimeSegment 298647597 298713133).card = 213 := by
  simpa using combineTwinPrimeSegments (by decide : 298647597 ≤ 298680365)
    (by decide : 298680365 ≤ 298713133) block2 block3

theorem join_1_0 : (twinPrimeSegment 298582061 298713133).card = 440 := by
  simpa using combineTwinPrimeSegments (by decide : 298582061 ≤ 298647597)
    (by decide : 298647597 ≤ 298713133) join_0_0 join_0_1

theorem total : (twinPrimeSegment 298582061 298713133).card = 440 := join_1_0

end S142C06
end Sude.GeneratedTwinScan
