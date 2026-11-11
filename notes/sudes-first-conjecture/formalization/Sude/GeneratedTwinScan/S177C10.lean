import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S177C10
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19301)) 372506669 372539437 = 104 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 372506669 372539437).card = 104 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19301 372506669 372539437
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19302)) 372539437 372572205 = 109 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 372539437 372572205).card = 109 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19302 372539437 372572205
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19302)) 372572205 372604973 = 115 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 372572205 372604973).card = 115 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19302 372572205 372604973
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19303)) 372604973 372637741 = 107 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 372604973 372637741).card = 107 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19303 372604973 372637741
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 372506669 372572205).card = 213 := by
  simpa using combineTwinPrimeSegments (by decide : 372506669 ≤ 372539437)
    (by decide : 372539437 ≤ 372572205) block0 block1

theorem join_0_1 : (twinPrimeSegment 372572205 372637741).card = 222 := by
  simpa using combineTwinPrimeSegments (by decide : 372572205 ≤ 372604973)
    (by decide : 372604973 ≤ 372637741) block2 block3

theorem join_1_0 : (twinPrimeSegment 372506669 372637741).card = 435 := by
  simpa using combineTwinPrimeSegments (by decide : 372506669 ≤ 372572205)
    (by decide : 372572205 ≤ 372637741) join_0_0 join_0_1

theorem total : (twinPrimeSegment 372506669 372637741).card = 435 := join_1_0

end S177C10
end Sude.GeneratedTwinScan
