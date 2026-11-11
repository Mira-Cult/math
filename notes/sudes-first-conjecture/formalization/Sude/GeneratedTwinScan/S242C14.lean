import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S242C14
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22569)) 509345837 509378605 = 101 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 509345837 509378605).card = 101 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22569 509345837 509378605
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22570)) 509378605 509411373 = 127 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 509378605 509411373).card = 127 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22570 509378605 509411373
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22570)) 509411373 509444141 = 94 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 509411373 509444141).card = 94 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22570 509411373 509444141
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22571)) 509444141 509476909 = 109 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 509444141 509476909).card = 109 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22571 509444141 509476909
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 509345837 509411373).card = 228 := by
  simpa using combineTwinPrimeSegments (by decide : 509345837 ≤ 509378605)
    (by decide : 509378605 ≤ 509411373) block0 block1

theorem join_0_1 : (twinPrimeSegment 509411373 509476909).card = 203 := by
  simpa using combineTwinPrimeSegments (by decide : 509411373 ≤ 509444141)
    (by decide : 509444141 ≤ 509476909) block2 block3

theorem join_1_0 : (twinPrimeSegment 509345837 509476909).card = 431 := by
  simpa using combineTwinPrimeSegments (by decide : 509345837 ≤ 509411373)
    (by decide : 509411373 ≤ 509476909) join_0_0 join_0_1

theorem total : (twinPrimeSegment 509345837 509476909).card = 431 := join_1_0

end S242C14
end Sude.GeneratedTwinScan
