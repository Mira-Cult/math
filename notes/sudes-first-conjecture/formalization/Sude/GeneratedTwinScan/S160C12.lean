import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S160C12
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18361)) 337117229 337149997 = 106 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 337117229 337149997).card = 106 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18361 337117229 337149997
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18362)) 337149997 337182765 = 130 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 337149997 337182765).card = 130 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18362 337149997 337182765
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18363)) 337182765 337215533 = 107 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 337182765 337215533).card = 107 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18363 337182765 337215533
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18364)) 337215533 337248301 = 116 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 337215533 337248301).card = 116 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18364 337215533 337248301
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 337117229 337182765).card = 236 := by
  simpa using combineTwinPrimeSegments (by decide : 337117229 ≤ 337149997)
    (by decide : 337149997 ≤ 337182765) block0 block1

theorem join_0_1 : (twinPrimeSegment 337182765 337248301).card = 223 := by
  simpa using combineTwinPrimeSegments (by decide : 337182765 ≤ 337215533)
    (by decide : 337215533 ≤ 337248301) block2 block3

theorem join_1_0 : (twinPrimeSegment 337117229 337248301).card = 459 := by
  simpa using combineTwinPrimeSegments (by decide : 337117229 ≤ 337182765)
    (by decide : 337182765 ≤ 337248301) join_0_0 join_0_1

theorem total : (twinPrimeSegment 337117229 337248301).card = 459 := join_1_0

end S160C12
end Sude.GeneratedTwinScan
