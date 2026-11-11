import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S204C02
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20690)) 428081197 428113965 = 102 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 428081197 428113965).card = 102 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20690 428081197 428113965
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20691)) 428113965 428146733 = 105 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 428113965 428146733).card = 105 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20691 428113965 428146733
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20692)) 428146733 428179501 = 96 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 428146733 428179501).card = 96 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20692 428146733 428179501
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20693)) 428179501 428212269 = 118 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 428179501 428212269).card = 118 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20693 428179501 428212269
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 428081197 428146733).card = 207 := by
  simpa using combineTwinPrimeSegments (by decide : 428081197 ≤ 428113965)
    (by decide : 428113965 ≤ 428146733) block0 block1

theorem join_0_1 : (twinPrimeSegment 428146733 428212269).card = 214 := by
  simpa using combineTwinPrimeSegments (by decide : 428146733 ≤ 428179501)
    (by decide : 428179501 ≤ 428212269) block2 block3

theorem join_1_0 : (twinPrimeSegment 428081197 428212269).card = 421 := by
  simpa using combineTwinPrimeSegments (by decide : 428081197 ≤ 428146733)
    (by decide : 428146733 ≤ 428212269) join_0_0 join_0_1

theorem total : (twinPrimeSegment 428081197 428212269).card = 421 := join_1_0

end S204C02
end Sude.GeneratedTwinScan
