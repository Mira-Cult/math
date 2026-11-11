import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S235C15
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22244)) 494796845 494829613 = 103 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 494796845 494829613).card = 103 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22244 494796845 494829613
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22245)) 494829613 494862381 = 102 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 494829613 494862381).card = 102 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22245 494829613 494862381
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22246)) 494862381 494895149 = 111 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 494862381 494895149).card = 111 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22246 494862381 494895149
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22246)) 494895149 494927917 = 120 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 494895149 494927917).card = 120 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22246 494895149 494927917
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 494796845 494862381).card = 205 := by
  simpa using combineTwinPrimeSegments (by decide : 494796845 ≤ 494829613)
    (by decide : 494829613 ≤ 494862381) block0 block1

theorem join_0_1 : (twinPrimeSegment 494862381 494927917).card = 231 := by
  simpa using combineTwinPrimeSegments (by decide : 494862381 ≤ 494895149)
    (by decide : 494895149 ≤ 494927917) block2 block3

theorem join_1_0 : (twinPrimeSegment 494796845 494927917).card = 436 := by
  simpa using combineTwinPrimeSegments (by decide : 494796845 ≤ 494862381)
    (by decide : 494862381 ≤ 494927917) join_0_0 join_0_1

theorem total : (twinPrimeSegment 494796845 494927917).card = 436 := join_1_0

end S235C15
end Sude.GeneratedTwinScan
