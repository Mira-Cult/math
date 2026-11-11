import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S166C08
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18687)) 349175853 349208621 = 127 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 349175853 349208621).card = 127 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18687 349175853 349208621
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18688)) 349208621 349241389 = 112 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 349208621 349241389).card = 112 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18688 349208621 349241389
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18688)) 349241389 349274157 = 123 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 349241389 349274157).card = 123 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18688 349241389 349274157
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18689)) 349274157 349306925 = 92 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 349274157 349306925).card = 92 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18689 349274157 349306925
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 349175853 349241389).card = 239 := by
  simpa using combineTwinPrimeSegments (by decide : 349175853 ≤ 349208621)
    (by decide : 349208621 ≤ 349241389) block0 block1

theorem join_0_1 : (twinPrimeSegment 349241389 349306925).card = 215 := by
  simpa using combineTwinPrimeSegments (by decide : 349241389 ≤ 349274157)
    (by decide : 349274157 ≤ 349306925) block2 block3

theorem join_1_0 : (twinPrimeSegment 349175853 349306925).card = 454 := by
  simpa using combineTwinPrimeSegments (by decide : 349175853 ≤ 349241389)
    (by decide : 349241389 ≤ 349306925) join_0_0 join_0_1

theorem total : (twinPrimeSegment 349175853 349306925).card = 454 := join_1_0

end S166C08
end Sude.GeneratedTwinScan
