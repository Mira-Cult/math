import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S198C11
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20413)) 416677933 416710701 = 114 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 416677933 416710701).card = 114 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20413 416677933 416710701
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20414)) 416710701 416743469 = 112 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 416710701 416743469).card = 112 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20414 416710701 416743469
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20415)) 416743469 416776237 = 116 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 416743469 416776237).card = 116 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20415 416743469 416776237
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20415)) 416776237 416809005 = 105 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 416776237 416809005).card = 105 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20415 416776237 416809005
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 416677933 416743469).card = 226 := by
  simpa using combineTwinPrimeSegments (by decide : 416677933 ≤ 416710701)
    (by decide : 416710701 ≤ 416743469) block0 block1

theorem join_0_1 : (twinPrimeSegment 416743469 416809005).card = 221 := by
  simpa using combineTwinPrimeSegments (by decide : 416743469 ≤ 416776237)
    (by decide : 416776237 ≤ 416809005) block2 block3

theorem join_1_0 : (twinPrimeSegment 416677933 416809005).card = 447 := by
  simpa using combineTwinPrimeSegments (by decide : 416677933 ≤ 416743469)
    (by decide : 416743469 ≤ 416809005) join_0_0 join_0_1

theorem total : (twinPrimeSegment 416677933 416809005).card = 447 := join_1_0

end S198C11
end Sude.GeneratedTwinScan
