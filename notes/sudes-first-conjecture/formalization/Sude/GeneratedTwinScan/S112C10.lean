import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S112C10
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15369)) 236191789 236224557 = 120 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 236191789 236224557).card = 120 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15369 236191789 236224557
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15370)) 236224557 236257325 = 126 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 236224557 236257325).card = 126 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15370 236224557 236257325
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15371)) 236257325 236290093 = 115 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 236257325 236290093).card = 115 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15371 236257325 236290093
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15372)) 236290093 236322861 = 120 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 236290093 236322861).card = 120 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15372 236290093 236322861
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 236191789 236257325).card = 246 := by
  simpa using combineTwinPrimeSegments (by decide : 236191789 ≤ 236224557)
    (by decide : 236224557 ≤ 236257325) block0 block1

theorem join_0_1 : (twinPrimeSegment 236257325 236322861).card = 235 := by
  simpa using combineTwinPrimeSegments (by decide : 236257325 ≤ 236290093)
    (by decide : 236290093 ≤ 236322861) block2 block3

theorem join_1_0 : (twinPrimeSegment 236191789 236322861).card = 481 := by
  simpa using combineTwinPrimeSegments (by decide : 236191789 ≤ 236257325)
    (by decide : 236257325 ≤ 236322861) join_0_0 join_0_1

theorem total : (twinPrimeSegment 236191789 236322861).card = 481 := join_1_0

end S112C10
end Sude.GeneratedTwinScan
