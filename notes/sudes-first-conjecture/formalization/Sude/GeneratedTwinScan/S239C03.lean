import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S239C03
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22397)) 501612589 501645357 = 111 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 501612589 501645357).card = 111 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22397 501612589 501645357
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22398)) 501645357 501678125 = 84 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 501645357 501678125).card = 84 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22398 501645357 501678125
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22398)) 501678125 501710893 = 100 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 501678125 501710893).card = 100 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22398 501678125 501710893
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22399)) 501710893 501743661 = 88 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 501710893 501743661).card = 88 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22399 501710893 501743661
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 501612589 501678125).card = 195 := by
  simpa using combineTwinPrimeSegments (by decide : 501612589 ≤ 501645357)
    (by decide : 501645357 ≤ 501678125) block0 block1

theorem join_0_1 : (twinPrimeSegment 501678125 501743661).card = 188 := by
  simpa using combineTwinPrimeSegments (by decide : 501678125 ≤ 501710893)
    (by decide : 501710893 ≤ 501743661) block2 block3

theorem join_1_0 : (twinPrimeSegment 501612589 501743661).card = 383 := by
  simpa using combineTwinPrimeSegments (by decide : 501612589 ≤ 501678125)
    (by decide : 501678125 ≤ 501743661) join_0_0 join_0_1

theorem total : (twinPrimeSegment 501612589 501743661).card = 383 := join_1_0

end S239C03
end Sude.GeneratedTwinScan
