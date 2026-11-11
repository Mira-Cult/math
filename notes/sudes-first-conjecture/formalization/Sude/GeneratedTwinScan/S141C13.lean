import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S141C13
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17246)) 297402413 297435181 = 110 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 297402413 297435181).card = 110 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17246 297402413 297435181
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17247)) 297435181 297467949 = 128 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 297435181 297467949).card = 128 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17247 297435181 297467949
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17248)) 297467949 297500717 = 102 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 297467949 297500717).card = 102 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17248 297467949 297500717
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17249)) 297500717 297533485 = 127 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 297500717 297533485).card = 127 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17249 297500717 297533485
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 297402413 297467949).card = 238 := by
  simpa using combineTwinPrimeSegments (by decide : 297402413 ≤ 297435181)
    (by decide : 297435181 ≤ 297467949) block0 block1

theorem join_0_1 : (twinPrimeSegment 297467949 297533485).card = 229 := by
  simpa using combineTwinPrimeSegments (by decide : 297467949 ≤ 297500717)
    (by decide : 297500717 ≤ 297533485) block2 block3

theorem join_1_0 : (twinPrimeSegment 297402413 297533485).card = 467 := by
  simpa using combineTwinPrimeSegments (by decide : 297402413 ≤ 297467949)
    (by decide : 297467949 ≤ 297533485) join_0_0 join_0_1

theorem total : (twinPrimeSegment 297402413 297533485).card = 467 := join_1_0

end S141C13
end Sude.GeneratedTwinScan
