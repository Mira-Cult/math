import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S112C12
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15378)) 236453933 236486701 = 128 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 236453933 236486701).card = 128 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15378 236453933 236486701
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15379)) 236486701 236519469 = 108 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 236486701 236519469).card = 108 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15379 236486701 236519469
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15380)) 236519469 236552237 = 125 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 236519469 236552237).card = 125 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15380 236519469 236552237
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15381)) 236552237 236585005 = 124 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 236552237 236585005).card = 124 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15381 236552237 236585005
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 236453933 236519469).card = 236 := by
  simpa using combineTwinPrimeSegments (by decide : 236453933 ≤ 236486701)
    (by decide : 236486701 ≤ 236519469) block0 block1

theorem join_0_1 : (twinPrimeSegment 236519469 236585005).card = 249 := by
  simpa using combineTwinPrimeSegments (by decide : 236519469 ≤ 236552237)
    (by decide : 236552237 ≤ 236585005) block2 block3

theorem join_1_0 : (twinPrimeSegment 236453933 236585005).card = 485 := by
  simpa using combineTwinPrimeSegments (by decide : 236453933 ≤ 236519469)
    (by decide : 236519469 ≤ 236585005) join_0_0 join_0_1

theorem total : (twinPrimeSegment 236453933 236585005).card = 485 := join_1_0

end S112C12
end Sude.GeneratedTwinScan
