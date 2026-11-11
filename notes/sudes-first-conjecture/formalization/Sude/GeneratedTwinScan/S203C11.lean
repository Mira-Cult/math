import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S203C11
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20668)) 427163693 427196461 = 100 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 427163693 427196461).card = 100 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20668 427163693 427196461
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20669)) 427196461 427229229 = 110 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 427196461 427229229).card = 110 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20669 427196461 427229229
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20670)) 427229229 427261997 = 98 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 427229229 427261997).card = 98 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20670 427229229 427261997
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20671)) 427261997 427294765 = 109 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 427261997 427294765).card = 109 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20671 427261997 427294765
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 427163693 427229229).card = 210 := by
  simpa using combineTwinPrimeSegments (by decide : 427163693 ≤ 427196461)
    (by decide : 427196461 ≤ 427229229) block0 block1

theorem join_0_1 : (twinPrimeSegment 427229229 427294765).card = 207 := by
  simpa using combineTwinPrimeSegments (by decide : 427229229 ≤ 427261997)
    (by decide : 427261997 ≤ 427294765) block2 block3

theorem join_1_0 : (twinPrimeSegment 427163693 427294765).card = 417 := by
  simpa using combineTwinPrimeSegments (by decide : 427163693 ≤ 427229229)
    (by decide : 427229229 ≤ 427294765) join_0_0 join_0_1

theorem total : (twinPrimeSegment 427163693 427294765).card = 417 := join_1_0

end S203C11
end Sude.GeneratedTwinScan
