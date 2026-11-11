import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S235C10
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22230)) 494141485 494174253 = 101 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 494141485 494174253).card = 101 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22230 494141485 494174253
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22230)) 494174253 494207021 = 114 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 494174253 494207021).card = 114 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22230 494174253 494207021
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22231)) 494207021 494239789 = 94 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 494207021 494239789).card = 94 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22231 494207021 494239789
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22232)) 494239789 494272557 = 119 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 494239789 494272557).card = 119 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22232 494239789 494272557
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 494141485 494207021).card = 215 := by
  simpa using combineTwinPrimeSegments (by decide : 494141485 ≤ 494174253)
    (by decide : 494174253 ≤ 494207021) block0 block1

theorem join_0_1 : (twinPrimeSegment 494207021 494272557).card = 213 := by
  simpa using combineTwinPrimeSegments (by decide : 494207021 ≤ 494239789)
    (by decide : 494239789 ≤ 494272557) block2 block3

theorem join_1_0 : (twinPrimeSegment 494141485 494272557).card = 428 := by
  simpa using combineTwinPrimeSegments (by decide : 494141485 ≤ 494207021)
    (by decide : 494207021 ≤ 494272557) join_0_0 join_0_1

theorem total : (twinPrimeSegment 494141485 494272557).card = 428 := join_1_0

end S235C10
end Sude.GeneratedTwinScan
