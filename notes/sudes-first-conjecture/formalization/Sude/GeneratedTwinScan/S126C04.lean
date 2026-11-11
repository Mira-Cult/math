import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S126C04
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16272)) 264765485 264798253 = 121 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 264765485 264798253).card = 121 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16272 264765485 264798253
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16273)) 264798253 264831021 = 113 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 264798253 264831021).card = 113 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16273 264798253 264831021
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16274)) 264831021 264863789 = 138 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 264831021 264863789).card = 138 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16274 264831021 264863789
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16275)) 264863789 264896557 = 110 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 264863789 264896557).card = 110 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16275 264863789 264896557
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 264765485 264831021).card = 234 := by
  simpa using combineTwinPrimeSegments (by decide : 264765485 ≤ 264798253)
    (by decide : 264798253 ≤ 264831021) block0 block1

theorem join_0_1 : (twinPrimeSegment 264831021 264896557).card = 248 := by
  simpa using combineTwinPrimeSegments (by decide : 264831021 ≤ 264863789)
    (by decide : 264863789 ≤ 264896557) block2 block3

theorem join_1_0 : (twinPrimeSegment 264765485 264896557).card = 482 := by
  simpa using combineTwinPrimeSegments (by decide : 264765485 ≤ 264831021)
    (by decide : 264831021 ≤ 264896557) join_0_0 join_0_1

theorem total : (twinPrimeSegment 264765485 264896557).card = 482 := join_1_0

end S126C04
end Sude.GeneratedTwinScan
