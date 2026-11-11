import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S115C03
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15543)) 241565741 241598509 = 131 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 241565741 241598509).card = 131 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15543 241565741 241598509
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15544)) 241598509 241631277 = 120 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 241598509 241631277).card = 120 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15544 241598509 241631277
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15545)) 241631277 241664045 = 119 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 241631277 241664045).card = 119 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15545 241631277 241664045
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15546)) 241664045 241696813 = 112 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 241664045 241696813).card = 112 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15546 241664045 241696813
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 241565741 241631277).card = 251 := by
  simpa using combineTwinPrimeSegments (by decide : 241565741 ≤ 241598509)
    (by decide : 241598509 ≤ 241631277) block0 block1

theorem join_0_1 : (twinPrimeSegment 241631277 241696813).card = 231 := by
  simpa using combineTwinPrimeSegments (by decide : 241631277 ≤ 241664045)
    (by decide : 241664045 ≤ 241696813) block2 block3

theorem join_1_0 : (twinPrimeSegment 241565741 241696813).card = 482 := by
  simpa using combineTwinPrimeSegments (by decide : 241565741 ≤ 241631277)
    (by decide : 241631277 ≤ 241696813) join_0_0 join_0_1

theorem total : (twinPrimeSegment 241565741 241696813).card = 482 := join_1_0

end S115C03
end Sude.GeneratedTwinScan
