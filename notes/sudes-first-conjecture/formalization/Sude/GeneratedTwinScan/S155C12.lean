import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S155C12
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18073)) 326631469 326664237 = 115 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 326631469 326664237).card = 115 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18073 326631469 326664237
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18074)) 326664237 326697005 = 106 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 326664237 326697005).card = 106 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18074 326664237 326697005
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18075)) 326697005 326729773 = 112 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 326697005 326729773).card = 112 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18075 326697005 326729773
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18076)) 326729773 326762541 = 97 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 326729773 326762541).card = 97 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18076 326729773 326762541
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 326631469 326697005).card = 221 := by
  simpa using combineTwinPrimeSegments (by decide : 326631469 ≤ 326664237)
    (by decide : 326664237 ≤ 326697005) block0 block1

theorem join_0_1 : (twinPrimeSegment 326697005 326762541).card = 209 := by
  simpa using combineTwinPrimeSegments (by decide : 326697005 ≤ 326729773)
    (by decide : 326729773 ≤ 326762541) block2 block3

theorem join_1_0 : (twinPrimeSegment 326631469 326762541).card = 430 := by
  simpa using combineTwinPrimeSegments (by decide : 326631469 ≤ 326697005)
    (by decide : 326697005 ≤ 326762541) join_0_0 join_0_1

theorem total : (twinPrimeSegment 326631469 326762541).card = 430 := join_1_0

end S155C12
end Sude.GeneratedTwinScan
