import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S128C02
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16392)) 268697645 268730413 = 115 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 268697645 268730413).card = 115 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16392 268697645 268730413
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16393)) 268730413 268763181 = 113 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 268730413 268763181).card = 113 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16393 268730413 268763181
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16394)) 268763181 268795949 = 101 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 268763181 268795949).card = 101 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16394 268763181 268795949
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16395)) 268795949 268828717 = 102 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 268795949 268828717).card = 102 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16395 268795949 268828717
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 268697645 268763181).card = 228 := by
  simpa using combineTwinPrimeSegments (by decide : 268697645 ≤ 268730413)
    (by decide : 268730413 ≤ 268763181) block0 block1

theorem join_0_1 : (twinPrimeSegment 268763181 268828717).card = 203 := by
  simpa using combineTwinPrimeSegments (by decide : 268763181 ≤ 268795949)
    (by decide : 268795949 ≤ 268828717) block2 block3

theorem join_1_0 : (twinPrimeSegment 268697645 268828717).card = 431 := by
  simpa using combineTwinPrimeSegments (by decide : 268697645 ≤ 268763181)
    (by decide : 268763181 ≤ 268828717) join_0_0 join_0_1

theorem total : (twinPrimeSegment 268697645 268828717).card = 431 := join_1_0

end S128C02
end Sude.GeneratedTwinScan
