import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S148C01
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17622)) 310509613 310542381 = 124 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 310509613 310542381).card = 124 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17622 310509613 310542381
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17623)) 310542381 310575149 = 116 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 310542381 310575149).card = 116 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17623 310542381 310575149
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17624)) 310575149 310607917 = 115 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 310575149 310607917).card = 115 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17624 310575149 310607917
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17625)) 310607917 310640685 = 119 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 310607917 310640685).card = 119 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17625 310607917 310640685
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 310509613 310575149).card = 240 := by
  simpa using combineTwinPrimeSegments (by decide : 310509613 ≤ 310542381)
    (by decide : 310542381 ≤ 310575149) block0 block1

theorem join_0_1 : (twinPrimeSegment 310575149 310640685).card = 234 := by
  simpa using combineTwinPrimeSegments (by decide : 310575149 ≤ 310607917)
    (by decide : 310607917 ≤ 310640685) block2 block3

theorem join_1_0 : (twinPrimeSegment 310509613 310640685).card = 474 := by
  simpa using combineTwinPrimeSegments (by decide : 310509613 ≤ 310575149)
    (by decide : 310575149 ≤ 310640685) join_0_0 join_0_1

theorem total : (twinPrimeSegment 310509613 310640685).card = 474 := join_1_0

end S148C01
end Sude.GeneratedTwinScan
