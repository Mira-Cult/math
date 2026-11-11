import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S159C11
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18300)) 334889005 334921773 = 106 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 334889005 334921773).card = 106 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18300 334889005 334921773
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18301)) 334921773 334954541 = 95 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 334921773 334954541).card = 95 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18301 334921773 334954541
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18302)) 334954541 334987309 = 116 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 334954541 334987309).card = 116 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18302 334954541 334987309
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18303)) 334987309 335020077 = 122 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 334987309 335020077).card = 122 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18303 334987309 335020077
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 334889005 334954541).card = 201 := by
  simpa using combineTwinPrimeSegments (by decide : 334889005 ≤ 334921773)
    (by decide : 334921773 ≤ 334954541) block0 block1

theorem join_0_1 : (twinPrimeSegment 334954541 335020077).card = 238 := by
  simpa using combineTwinPrimeSegments (by decide : 334954541 ≤ 334987309)
    (by decide : 334987309 ≤ 335020077) block2 block3

theorem join_1_0 : (twinPrimeSegment 334889005 335020077).card = 439 := by
  simpa using combineTwinPrimeSegments (by decide : 334889005 ≤ 334954541)
    (by decide : 334954541 ≤ 335020077) join_0_0 join_0_1

theorem total : (twinPrimeSegment 334889005 335020077).card = 439 := join_1_0

end S159C11
end Sude.GeneratedTwinScan
