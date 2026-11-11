import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S193C14
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20164)) 406585389 406618157 = 106 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 406585389 406618157).card = 106 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20164 406585389 406618157
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20165)) 406618157 406650925 = 96 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 406618157 406650925).card = 96 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20165 406618157 406650925
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20166)) 406650925 406683693 = 101 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 406650925 406683693).card = 101 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20166 406650925 406683693
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20167)) 406683693 406716461 = 109 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 406683693 406716461).card = 109 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20167 406683693 406716461
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 406585389 406650925).card = 202 := by
  simpa using combineTwinPrimeSegments (by decide : 406585389 ≤ 406618157)
    (by decide : 406618157 ≤ 406650925) block0 block1

theorem join_0_1 : (twinPrimeSegment 406650925 406716461).card = 210 := by
  simpa using combineTwinPrimeSegments (by decide : 406650925 ≤ 406683693)
    (by decide : 406683693 ≤ 406716461) block2 block3

theorem join_1_0 : (twinPrimeSegment 406585389 406716461).card = 412 := by
  simpa using combineTwinPrimeSegments (by decide : 406585389 ≤ 406650925)
    (by decide : 406650925 ≤ 406716461) join_0_0 join_0_1

theorem total : (twinPrimeSegment 406585389 406716461).card = 412 := join_1_0

end S193C14
end Sude.GeneratedTwinScan
