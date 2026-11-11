import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S218C08
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21407)) 458227757 458260525 = 103 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 458227757 458260525).card = 103 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21407 458227757 458260525
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21407)) 458260525 458293293 = 102 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 458260525 458293293).card = 102 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21407 458260525 458293293
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21408)) 458293293 458326061 = 108 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 458293293 458326061).card = 108 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21408 458293293 458326061
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21409)) 458326061 458358829 = 119 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 458326061 458358829).card = 119 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21409 458326061 458358829
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 458227757 458293293).card = 205 := by
  simpa using combineTwinPrimeSegments (by decide : 458227757 ≤ 458260525)
    (by decide : 458260525 ≤ 458293293) block0 block1

theorem join_0_1 : (twinPrimeSegment 458293293 458358829).card = 227 := by
  simpa using combineTwinPrimeSegments (by decide : 458293293 ≤ 458326061)
    (by decide : 458326061 ≤ 458358829) block2 block3

theorem join_1_0 : (twinPrimeSegment 458227757 458358829).card = 432 := by
  simpa using combineTwinPrimeSegments (by decide : 458227757 ≤ 458293293)
    (by decide : 458293293 ≤ 458358829) join_0_0 join_0_1

theorem total : (twinPrimeSegment 458227757 458358829).card = 432 := join_1_0

end S218C08
end Sude.GeneratedTwinScan
