import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S158C09
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18236)) 332529709 332562477 = 122 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 332529709 332562477).card = 122 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18236 332529709 332562477
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18237)) 332562477 332595245 = 111 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 332562477 332595245).card = 111 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18237 332562477 332595245
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18238)) 332595245 332628013 = 129 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 332595245 332628013).card = 129 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18238 332595245 332628013
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18238)) 332628013 332660781 = 103 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 332628013 332660781).card = 103 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18238 332628013 332660781
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 332529709 332595245).card = 233 := by
  simpa using combineTwinPrimeSegments (by decide : 332529709 ≤ 332562477)
    (by decide : 332562477 ≤ 332595245) block0 block1

theorem join_0_1 : (twinPrimeSegment 332595245 332660781).card = 232 := by
  simpa using combineTwinPrimeSegments (by decide : 332595245 ≤ 332628013)
    (by decide : 332628013 ≤ 332660781) block2 block3

theorem join_1_0 : (twinPrimeSegment 332529709 332660781).card = 465 := by
  simpa using combineTwinPrimeSegments (by decide : 332529709 ≤ 332595245)
    (by decide : 332595245 ≤ 332660781) join_0_0 join_0_1

theorem total : (twinPrimeSegment 332529709 332660781).card = 465 := join_1_0

end S158C09
end Sude.GeneratedTwinScan
