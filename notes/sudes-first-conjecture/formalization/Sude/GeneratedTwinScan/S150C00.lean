import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S150C00
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17737)) 314572845 314605613 = 119 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 314572845 314605613).card = 119 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17737 314572845 314605613
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17738)) 314605613 314638381 = 125 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 314605613 314638381).card = 125 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17738 314605613 314638381
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17738)) 314638381 314671149 = 124 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 314638381 314671149).card = 124 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17738 314638381 314671149
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17739)) 314671149 314703917 = 117 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 314671149 314703917).card = 117 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17739 314671149 314703917
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 314572845 314638381).card = 244 := by
  simpa using combineTwinPrimeSegments (by decide : 314572845 ≤ 314605613)
    (by decide : 314605613 ≤ 314638381) block0 block1

theorem join_0_1 : (twinPrimeSegment 314638381 314703917).card = 241 := by
  simpa using combineTwinPrimeSegments (by decide : 314638381 ≤ 314671149)
    (by decide : 314671149 ≤ 314703917) block2 block3

theorem join_1_0 : (twinPrimeSegment 314572845 314703917).card = 485 := by
  simpa using combineTwinPrimeSegments (by decide : 314572845 ≤ 314638381)
    (by decide : 314638381 ≤ 314703917) join_0_0 join_0_1

theorem total : (twinPrimeSegment 314572845 314703917).card = 485 := join_1_0

end S150C00
end Sude.GeneratedTwinScan
