import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S115C00
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15530)) 241172525 241205293 = 121 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 241172525 241205293).card = 121 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15530 241172525 241205293
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15531)) 241205293 241238061 = 131 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 241205293 241238061).card = 131 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15531 241205293 241238061
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15532)) 241238061 241270829 = 114 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 241238061 241270829).card = 114 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15532 241238061 241270829
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15533)) 241270829 241303597 = 123 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 241270829 241303597).card = 123 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15533 241270829 241303597
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 241172525 241238061).card = 252 := by
  simpa using combineTwinPrimeSegments (by decide : 241172525 ≤ 241205293)
    (by decide : 241205293 ≤ 241238061) block0 block1

theorem join_0_1 : (twinPrimeSegment 241238061 241303597).card = 237 := by
  simpa using combineTwinPrimeSegments (by decide : 241238061 ≤ 241270829)
    (by decide : 241270829 ≤ 241303597) block2 block3

theorem join_1_0 : (twinPrimeSegment 241172525 241303597).card = 489 := by
  simpa using combineTwinPrimeSegments (by decide : 241172525 ≤ 241238061)
    (by decide : 241238061 ≤ 241303597) join_0_0 join_0_1

theorem total : (twinPrimeSegment 241172525 241303597).card = 489 := join_1_0

end S115C00
end Sude.GeneratedTwinScan
