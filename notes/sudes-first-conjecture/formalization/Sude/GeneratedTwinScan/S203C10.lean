import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S203C10
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20665)) 427032621 427065389 = 114 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 427032621 427065389).card = 114 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20665 427032621 427065389
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20666)) 427065389 427098157 = 112 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 427065389 427098157).card = 112 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20666 427065389 427098157
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20667)) 427098157 427130925 = 113 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 427098157 427130925).card = 113 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20667 427098157 427130925
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20667)) 427130925 427163693 = 110 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 427130925 427163693).card = 110 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20667 427130925 427163693
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 427032621 427098157).card = 226 := by
  simpa using combineTwinPrimeSegments (by decide : 427032621 ≤ 427065389)
    (by decide : 427065389 ≤ 427098157) block0 block1

theorem join_0_1 : (twinPrimeSegment 427098157 427163693).card = 223 := by
  simpa using combineTwinPrimeSegments (by decide : 427098157 ≤ 427130925)
    (by decide : 427130925 ≤ 427163693) block2 block3

theorem join_1_0 : (twinPrimeSegment 427032621 427163693).card = 449 := by
  simpa using combineTwinPrimeSegments (by decide : 427032621 ≤ 427098157)
    (by decide : 427098157 ≤ 427163693) join_0_0 join_0_1

theorem total : (twinPrimeSegment 427032621 427163693).card = 449 := join_1_0

end S203C10
end Sude.GeneratedTwinScan
