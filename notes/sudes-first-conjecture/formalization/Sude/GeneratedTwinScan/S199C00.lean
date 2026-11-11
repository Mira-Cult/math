import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S199C00
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20429)) 417333293 417366061 = 116 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 417333293 417366061).card = 116 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20429 417333293 417366061
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20430)) 417366061 417398829 = 114 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 417366061 417398829).card = 114 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20430 417366061 417398829
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20431)) 417398829 417431597 = 112 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 417398829 417431597).card = 112 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20431 417398829 417431597
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20431)) 417431597 417464365 = 102 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 417431597 417464365).card = 102 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20431 417431597 417464365
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 417333293 417398829).card = 230 := by
  simpa using combineTwinPrimeSegments (by decide : 417333293 ≤ 417366061)
    (by decide : 417366061 ≤ 417398829) block0 block1

theorem join_0_1 : (twinPrimeSegment 417398829 417464365).card = 214 := by
  simpa using combineTwinPrimeSegments (by decide : 417398829 ≤ 417431597)
    (by decide : 417431597 ≤ 417464365) block2 block3

theorem join_1_0 : (twinPrimeSegment 417333293 417464365).card = 444 := by
  simpa using combineTwinPrimeSegments (by decide : 417333293 ≤ 417398829)
    (by decide : 417398829 ≤ 417464365) join_0_0 join_0_1

theorem total : (twinPrimeSegment 417333293 417464365).card = 444 := join_1_0

end S199C00
end Sude.GeneratedTwinScan
