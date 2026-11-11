import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S096C11
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14240)) 202768429 202801197 = 119 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 202768429 202801197).card = 119 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14240 202768429 202801197
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14241)) 202801197 202833965 = 125 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 202801197 202833965).card = 125 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14241 202801197 202833965
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14243)) 202833965 202866733 = 100 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 202833965 202866733).card = 100 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14243 202833965 202866733
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14244)) 202866733 202899501 = 117 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 202866733 202899501).card = 117 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14244 202866733 202899501
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 202768429 202833965).card = 244 := by
  simpa using combineTwinPrimeSegments (by decide : 202768429 ≤ 202801197)
    (by decide : 202801197 ≤ 202833965) block0 block1

theorem join_0_1 : (twinPrimeSegment 202833965 202899501).card = 217 := by
  simpa using combineTwinPrimeSegments (by decide : 202833965 ≤ 202866733)
    (by decide : 202866733 ≤ 202899501) block2 block3

theorem join_1_0 : (twinPrimeSegment 202768429 202899501).card = 461 := by
  simpa using combineTwinPrimeSegments (by decide : 202768429 ≤ 202833965)
    (by decide : 202833965 ≤ 202899501) join_0_0 join_0_1

theorem total : (twinPrimeSegment 202768429 202899501).card = 461 := join_1_0

end S096C11
end Sude.GeneratedTwinScan
