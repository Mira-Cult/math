import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S098C13
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14396)) 207224877 207257645 = 124 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 207224877 207257645).card = 124 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14396 207224877 207257645
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14397)) 207257645 207290413 = 106 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 207257645 207290413).card = 106 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14397 207257645 207290413
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14398)) 207290413 207323181 = 118 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 207290413 207323181).card = 118 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14398 207290413 207323181
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14399)) 207323181 207355949 = 128 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 207323181 207355949).card = 128 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14399 207323181 207355949
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 207224877 207290413).card = 230 := by
  simpa using combineTwinPrimeSegments (by decide : 207224877 ≤ 207257645)
    (by decide : 207257645 ≤ 207290413) block0 block1

theorem join_0_1 : (twinPrimeSegment 207290413 207355949).card = 246 := by
  simpa using combineTwinPrimeSegments (by decide : 207290413 ≤ 207323181)
    (by decide : 207323181 ≤ 207355949) block2 block3

theorem join_1_0 : (twinPrimeSegment 207224877 207355949).card = 476 := by
  simpa using combineTwinPrimeSegments (by decide : 207224877 ≤ 207290413)
    (by decide : 207290413 ≤ 207355949) join_0_0 join_0_1

theorem total : (twinPrimeSegment 207224877 207355949).card = 476 := join_1_0

end S098C13
end Sude.GeneratedTwinScan
