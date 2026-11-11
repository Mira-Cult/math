import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S081C12
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13094)) 171442221 171474989 = 120 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 171442221 171474989).card = 120 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13094 171442221 171474989
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13096)) 171474989 171507757 = 106 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 171474989 171507757).card = 106 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13096 171474989 171507757
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13097)) 171507757 171540525 = 131 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 171507757 171540525).card = 131 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13097 171507757 171540525
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13098)) 171540525 171573293 = 120 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 171540525 171573293).card = 120 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13098 171540525 171573293
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 171442221 171507757).card = 226 := by
  simpa using combineTwinPrimeSegments (by decide : 171442221 ≤ 171474989)
    (by decide : 171474989 ≤ 171507757) block0 block1

theorem join_0_1 : (twinPrimeSegment 171507757 171573293).card = 251 := by
  simpa using combineTwinPrimeSegments (by decide : 171507757 ≤ 171540525)
    (by decide : 171540525 ≤ 171573293) block2 block3

theorem join_1_0 : (twinPrimeSegment 171442221 171573293).card = 477 := by
  simpa using combineTwinPrimeSegments (by decide : 171442221 ≤ 171507757)
    (by decide : 171507757 ≤ 171573293) join_0_0 join_0_1

theorem total : (twinPrimeSegment 171442221 171573293).card = 477 := join_1_0

end S081C12
end Sude.GeneratedTwinScan
