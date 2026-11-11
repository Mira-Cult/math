import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S124C04
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16143)) 260571181 260603949 = 100 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 260571181 260603949).card = 100 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16143 260571181 260603949
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16144)) 260603949 260636717 = 131 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 260603949 260636717).card = 131 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16144 260603949 260636717
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16145)) 260636717 260669485 = 110 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 260636717 260669485).card = 110 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16145 260636717 260669485
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16146)) 260669485 260702253 = 120 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 260669485 260702253).card = 120 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16146 260669485 260702253
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 260571181 260636717).card = 231 := by
  simpa using combineTwinPrimeSegments (by decide : 260571181 ≤ 260603949)
    (by decide : 260603949 ≤ 260636717) block0 block1

theorem join_0_1 : (twinPrimeSegment 260636717 260702253).card = 230 := by
  simpa using combineTwinPrimeSegments (by decide : 260636717 ≤ 260669485)
    (by decide : 260669485 ≤ 260702253) block2 block3

theorem join_1_0 : (twinPrimeSegment 260571181 260702253).card = 461 := by
  simpa using combineTwinPrimeSegments (by decide : 260571181 ≤ 260636717)
    (by decide : 260636717 ≤ 260702253) join_0_0 join_0_1

theorem total : (twinPrimeSegment 260571181 260702253).card = 461 := join_1_0

end S124C04
end Sude.GeneratedTwinScan
