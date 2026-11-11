import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S187C07
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19827)) 393084973 393117741 = 96 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 393084973 393117741).card = 96 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19827 393084973 393117741
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19828)) 393117741 393150509 = 113 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 393117741 393150509).card = 113 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19828 393117741 393150509
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19828)) 393150509 393183277 = 115 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 393150509 393183277).card = 115 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19828 393150509 393183277
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19829)) 393183277 393216045 = 98 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 393183277 393216045).card = 98 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19829 393183277 393216045
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 393084973 393150509).card = 209 := by
  simpa using combineTwinPrimeSegments (by decide : 393084973 ≤ 393117741)
    (by decide : 393117741 ≤ 393150509) block0 block1

theorem join_0_1 : (twinPrimeSegment 393150509 393216045).card = 213 := by
  simpa using combineTwinPrimeSegments (by decide : 393150509 ≤ 393183277)
    (by decide : 393183277 ≤ 393216045) block2 block3

theorem join_1_0 : (twinPrimeSegment 393084973 393216045).card = 422 := by
  simpa using combineTwinPrimeSegments (by decide : 393084973 ≤ 393150509)
    (by decide : 393150509 ≤ 393216045) join_0_0 join_0_1

theorem total : (twinPrimeSegment 393084973 393216045).card = 422 := join_1_0

end S187C07
end Sude.GeneratedTwinScan
