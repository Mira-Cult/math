import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S095C03
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14129)) 199622701 199655469 = 126 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 199622701 199655469).card = 126 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14129 199622701 199655469
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14131)) 199655469 199688237 = 127 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 199655469 199688237).card = 127 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14131 199655469 199688237
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14132)) 199688237 199721005 = 129 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 199688237 199721005).card = 129 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14132 199688237 199721005
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14133)) 199721005 199753773 = 119 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 199721005 199753773).card = 119 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14133 199721005 199753773
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 199622701 199688237).card = 253 := by
  simpa using combineTwinPrimeSegments (by decide : 199622701 ≤ 199655469)
    (by decide : 199655469 ≤ 199688237) block0 block1

theorem join_0_1 : (twinPrimeSegment 199688237 199753773).card = 248 := by
  simpa using combineTwinPrimeSegments (by decide : 199688237 ≤ 199721005)
    (by decide : 199721005 ≤ 199753773) block2 block3

theorem join_1_0 : (twinPrimeSegment 199622701 199753773).card = 501 := by
  simpa using combineTwinPrimeSegments (by decide : 199622701 ≤ 199688237)
    (by decide : 199688237 ≤ 199753773) join_0_0 join_0_1

theorem total : (twinPrimeSegment 199622701 199753773).card = 501 := join_1_0

end S095C03
end Sude.GeneratedTwinScan
