import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S165C07
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18627)) 346947629 346980397 = 123 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 346947629 346980397).card = 123 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18627 346947629 346980397
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18628)) 346980397 347013165 = 125 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 346980397 347013165).card = 125 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18628 346980397 347013165
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18629)) 347013165 347045933 = 131 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 347013165 347045933).card = 131 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18629 347013165 347045933
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18630)) 347045933 347078701 = 115 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 347045933 347078701).card = 115 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18630 347045933 347078701
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 346947629 347013165).card = 248 := by
  simpa using combineTwinPrimeSegments (by decide : 346947629 ≤ 346980397)
    (by decide : 346980397 ≤ 347013165) block0 block1

theorem join_0_1 : (twinPrimeSegment 347013165 347078701).card = 246 := by
  simpa using combineTwinPrimeSegments (by decide : 347013165 ≤ 347045933)
    (by decide : 347045933 ≤ 347078701) block2 block3

theorem join_1_0 : (twinPrimeSegment 346947629 347078701).card = 494 := by
  simpa using combineTwinPrimeSegments (by decide : 346947629 ≤ 347013165)
    (by decide : 347013165 ≤ 347078701) join_0_0 join_0_1

theorem total : (twinPrimeSegment 346947629 347078701).card = 494 := join_1_0

end S165C07
end Sude.GeneratedTwinScan
