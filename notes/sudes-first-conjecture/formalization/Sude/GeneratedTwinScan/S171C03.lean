import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S171C03
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18948)) 359006253 359039021 = 110 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 359006253 359039021).card = 110 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18948 359006253 359039021
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18949)) 359039021 359071789 = 101 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 359039021 359071789).card = 101 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18949 359039021 359071789
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18950)) 359071789 359104557 = 116 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 359071789 359104557).card = 116 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18950 359071789 359104557
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18950)) 359104557 359137325 = 119 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 359104557 359137325).card = 119 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18950 359104557 359137325
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 359006253 359071789).card = 211 := by
  simpa using combineTwinPrimeSegments (by decide : 359006253 ≤ 359039021)
    (by decide : 359039021 ≤ 359071789) block0 block1

theorem join_0_1 : (twinPrimeSegment 359071789 359137325).card = 235 := by
  simpa using combineTwinPrimeSegments (by decide : 359071789 ≤ 359104557)
    (by decide : 359104557 ≤ 359137325) block2 block3

theorem join_1_0 : (twinPrimeSegment 359006253 359137325).card = 446 := by
  simpa using combineTwinPrimeSegments (by decide : 359006253 ≤ 359071789)
    (by decide : 359071789 ≤ 359137325) join_0_0 join_0_1

theorem total : (twinPrimeSegment 359006253 359137325).card = 446 := join_1_0

end S171C03
end Sude.GeneratedTwinScan
