import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S095C05
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14139)) 199884845 199917613 = 123 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 199884845 199917613).card = 123 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14139 199884845 199917613
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14140)) 199917613 199950381 = 136 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 199917613 199950381).card = 136 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14140 199917613 199950381
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14141)) 199950381 199983149 = 134 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 199950381 199983149).card = 134 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14141 199950381 199983149
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14142)) 199983149 200015917 = 101 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 199983149 200015917).card = 101 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14142 199983149 200015917
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 199884845 199950381).card = 259 := by
  simpa using combineTwinPrimeSegments (by decide : 199884845 ≤ 199917613)
    (by decide : 199917613 ≤ 199950381) block0 block1

theorem join_0_1 : (twinPrimeSegment 199950381 200015917).card = 235 := by
  simpa using combineTwinPrimeSegments (by decide : 199950381 ≤ 199983149)
    (by decide : 199983149 ≤ 200015917) block2 block3

theorem join_1_0 : (twinPrimeSegment 199884845 200015917).card = 494 := by
  simpa using combineTwinPrimeSegments (by decide : 199884845 ≤ 199950381)
    (by decide : 199950381 ≤ 200015917) join_0_0 join_0_1

theorem total : (twinPrimeSegment 199884845 200015917).card = 494 := join_1_0

end S095C05
end Sude.GeneratedTwinScan
