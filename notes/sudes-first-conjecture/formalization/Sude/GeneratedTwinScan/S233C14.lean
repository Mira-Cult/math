import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S233C14
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22147)) 490471469 490504237 = 119 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 490471469 490504237).card = 119 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22147 490471469 490504237
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22148)) 490504237 490537005 = 88 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 490504237 490537005).card = 88 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22148 490504237 490537005
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22148)) 490537005 490569773 = 109 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 490537005 490569773).card = 109 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22148 490537005 490569773
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22149)) 490569773 490602541 = 110 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 490569773 490602541).card = 110 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22149 490569773 490602541
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 490471469 490537005).card = 207 := by
  simpa using combineTwinPrimeSegments (by decide : 490471469 ≤ 490504237)
    (by decide : 490504237 ≤ 490537005) block0 block1

theorem join_0_1 : (twinPrimeSegment 490537005 490602541).card = 219 := by
  simpa using combineTwinPrimeSegments (by decide : 490537005 ≤ 490569773)
    (by decide : 490569773 ≤ 490602541) block2 block3

theorem join_1_0 : (twinPrimeSegment 490471469 490602541).card = 426 := by
  simpa using combineTwinPrimeSegments (by decide : 490471469 ≤ 490537005)
    (by decide : 490537005 ≤ 490602541) join_0_0 join_0_1

theorem total : (twinPrimeSegment 490471469 490602541).card = 426 := join_1_0

end S233C14
end Sude.GeneratedTwinScan
