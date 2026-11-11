import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S245C02
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22673)) 514064429 514097197 = 110 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 514064429 514097197).card = 110 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22673 514064429 514097197
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22674)) 514097197 514129965 = 117 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 514097197 514129965).card = 117 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22674 514097197 514129965
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22675)) 514129965 514162733 = 96 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 514129965 514162733).card = 96 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22675 514129965 514162733
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22675)) 514162733 514195501 = 124 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 514162733 514195501).card = 124 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22675 514162733 514195501
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 514064429 514129965).card = 227 := by
  simpa using combineTwinPrimeSegments (by decide : 514064429 ≤ 514097197)
    (by decide : 514097197 ≤ 514129965) block0 block1

theorem join_0_1 : (twinPrimeSegment 514129965 514195501).card = 220 := by
  simpa using combineTwinPrimeSegments (by decide : 514129965 ≤ 514162733)
    (by decide : 514162733 ≤ 514195501) block2 block3

theorem join_1_0 : (twinPrimeSegment 514064429 514195501).card = 447 := by
  simpa using combineTwinPrimeSegments (by decide : 514064429 ≤ 514129965)
    (by decide : 514129965 ≤ 514195501) join_0_0 join_0_1

theorem total : (twinPrimeSegment 514064429 514195501).card = 447 := join_1_0

end S245C02
end Sude.GeneratedTwinScan
