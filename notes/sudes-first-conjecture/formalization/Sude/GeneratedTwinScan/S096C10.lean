import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S096C10
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14236)) 202637357 202670125 = 129 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 202637357 202670125).card = 129 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14236 202637357 202670125
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14237)) 202670125 202702893 = 108 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 202670125 202702893).card = 108 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14237 202670125 202702893
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14238)) 202702893 202735661 = 110 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 202702893 202735661).card = 110 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14238 202702893 202735661
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14239)) 202735661 202768429 = 110 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 202735661 202768429).card = 110 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14239 202735661 202768429
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 202637357 202702893).card = 237 := by
  simpa using combineTwinPrimeSegments (by decide : 202637357 ≤ 202670125)
    (by decide : 202670125 ≤ 202702893) block0 block1

theorem join_0_1 : (twinPrimeSegment 202702893 202768429).card = 220 := by
  simpa using combineTwinPrimeSegments (by decide : 202702893 ≤ 202735661)
    (by decide : 202735661 ≤ 202768429) block2 block3

theorem join_1_0 : (twinPrimeSegment 202637357 202768429).card = 457 := by
  simpa using combineTwinPrimeSegments (by decide : 202637357 ≤ 202702893)
    (by decide : 202702893 ≤ 202768429) join_0_0 join_0_1

theorem total : (twinPrimeSegment 202637357 202768429).card = 457 := join_1_0

end S096C10
end Sude.GeneratedTwinScan
