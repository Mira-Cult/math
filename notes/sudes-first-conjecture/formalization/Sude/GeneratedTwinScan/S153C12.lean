import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S153C12
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17957)) 322437165 322469933 = 108 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 322437165 322469933).card = 108 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17957 322437165 322469933
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17958)) 322469933 322502701 = 130 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 322469933 322502701).card = 130 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17958 322469933 322502701
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17959)) 322502701 322535469 = 116 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 322502701 322535469).card = 116 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17959 322502701 322535469
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17960)) 322535469 322568237 = 113 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 322535469 322568237).card = 113 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17960 322535469 322568237
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 322437165 322502701).card = 238 := by
  simpa using combineTwinPrimeSegments (by decide : 322437165 ≤ 322469933)
    (by decide : 322469933 ≤ 322502701) block0 block1

theorem join_0_1 : (twinPrimeSegment 322502701 322568237).card = 229 := by
  simpa using combineTwinPrimeSegments (by decide : 322502701 ≤ 322535469)
    (by decide : 322535469 ≤ 322568237) block2 block3

theorem join_1_0 : (twinPrimeSegment 322437165 322568237).card = 467 := by
  simpa using combineTwinPrimeSegments (by decide : 322437165 ≤ 322502701)
    (by decide : 322502701 ≤ 322568237) join_0_0 join_0_1

theorem total : (twinPrimeSegment 322437165 322568237).card = 467 := join_1_0

end S153C12
end Sude.GeneratedTwinScan
