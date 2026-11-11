import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S180C02
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19436)) 377749549 377782317 = 101 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 377749549 377782317).card = 101 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19436 377749549 377782317
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19437)) 377782317 377815085 = 96 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 377782317 377815085).card = 96 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19437 377782317 377815085
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19438)) 377815085 377847853 = 116 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 377815085 377847853).card = 116 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19438 377815085 377847853
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19439)) 377847853 377880621 = 121 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 377847853 377880621).card = 121 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19439 377847853 377880621
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 377749549 377815085).card = 197 := by
  simpa using combineTwinPrimeSegments (by decide : 377749549 ≤ 377782317)
    (by decide : 377782317 ≤ 377815085) block0 block1

theorem join_0_1 : (twinPrimeSegment 377815085 377880621).card = 237 := by
  simpa using combineTwinPrimeSegments (by decide : 377815085 ≤ 377847853)
    (by decide : 377847853 ≤ 377880621) block2 block3

theorem join_1_0 : (twinPrimeSegment 377749549 377880621).card = 434 := by
  simpa using combineTwinPrimeSegments (by decide : 377749549 ≤ 377815085)
    (by decide : 377815085 ≤ 377880621) join_0_0 join_0_1

theorem total : (twinPrimeSegment 377749549 377880621).card = 434 := join_1_0

end S180C02
end Sude.GeneratedTwinScan
