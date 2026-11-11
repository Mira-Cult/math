import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S241C03
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22490)) 505806893 505839661 = 120 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 505806893 505839661).card = 120 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22490 505806893 505839661
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22491)) 505839661 505872429 = 105 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 505839661 505872429).card = 105 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22491 505839661 505872429
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22492)) 505872429 505905197 = 122 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 505872429 505905197).card = 122 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22492 505872429 505905197
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22493)) 505905197 505937965 = 106 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 505905197 505937965).card = 106 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22493 505905197 505937965
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 505806893 505872429).card = 225 := by
  simpa using combineTwinPrimeSegments (by decide : 505806893 ≤ 505839661)
    (by decide : 505839661 ≤ 505872429) block0 block1

theorem join_0_1 : (twinPrimeSegment 505872429 505937965).card = 228 := by
  simpa using combineTwinPrimeSegments (by decide : 505872429 ≤ 505905197)
    (by decide : 505905197 ≤ 505937965) block2 block3

theorem join_1_0 : (twinPrimeSegment 505806893 505937965).card = 453 := by
  simpa using combineTwinPrimeSegments (by decide : 505806893 ≤ 505872429)
    (by decide : 505872429 ≤ 505937965) join_0_0 join_0_1

theorem total : (twinPrimeSegment 505806893 505937965).card = 453 := join_1_0

end S241C03
end Sude.GeneratedTwinScan
