import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S235C01
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22203)) 492961837 492994605 = 112 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 492961837 492994605).card = 112 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22203 492961837 492994605
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22204)) 492994605 493027373 = 96 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 492994605 493027373).card = 96 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22204 492994605 493027373
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22204)) 493027373 493060141 = 93 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 493027373 493060141).card = 93 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22204 493027373 493060141
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22205)) 493060141 493092909 = 97 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 493060141 493092909).card = 97 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22205 493060141 493092909
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 492961837 493027373).card = 208 := by
  simpa using combineTwinPrimeSegments (by decide : 492961837 ≤ 492994605)
    (by decide : 492994605 ≤ 493027373) block0 block1

theorem join_0_1 : (twinPrimeSegment 493027373 493092909).card = 190 := by
  simpa using combineTwinPrimeSegments (by decide : 493027373 ≤ 493060141)
    (by decide : 493060141 ≤ 493092909) block2 block3

theorem join_1_0 : (twinPrimeSegment 492961837 493092909).card = 398 := by
  simpa using combineTwinPrimeSegments (by decide : 492961837 ≤ 493027373)
    (by decide : 493027373 ≤ 493092909) join_0_0 join_0_1

theorem total : (twinPrimeSegment 492961837 493092909).card = 398 := join_1_0

end S235C01
end Sude.GeneratedTwinScan
