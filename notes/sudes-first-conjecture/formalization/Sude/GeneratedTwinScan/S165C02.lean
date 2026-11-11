import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S165C02
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18609)) 346292269 346325037 = 131 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 346292269 346325037).card = 131 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18609 346292269 346325037
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18610)) 346325037 346357805 = 99 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 346325037 346357805).card = 99 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18610 346325037 346357805
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18611)) 346357805 346390573 = 103 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 346357805 346390573).card = 103 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18611 346357805 346390573
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18612)) 346390573 346423341 = 105 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 346390573 346423341).card = 105 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18612 346390573 346423341
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 346292269 346357805).card = 230 := by
  simpa using combineTwinPrimeSegments (by decide : 346292269 ≤ 346325037)
    (by decide : 346325037 ≤ 346357805) block0 block1

theorem join_0_1 : (twinPrimeSegment 346357805 346423341).card = 208 := by
  simpa using combineTwinPrimeSegments (by decide : 346357805 ≤ 346390573)
    (by decide : 346390573 ≤ 346423341) block2 block3

theorem join_1_0 : (twinPrimeSegment 346292269 346423341).card = 438 := by
  simpa using combineTwinPrimeSegments (by decide : 346292269 ≤ 346357805)
    (by decide : 346357805 ≤ 346423341) join_0_0 join_0_1

theorem total : (twinPrimeSegment 346292269 346423341).card = 438 := join_1_0

end S165C02
end Sude.GeneratedTwinScan
