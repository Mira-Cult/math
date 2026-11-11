import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S223C14
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21668)) 469499949 469532717 = 109 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 469499949 469532717).card = 109 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21668 469499949 469532717
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21669)) 469532717 469565485 = 120 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 469532717 469565485).card = 120 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21669 469532717 469565485
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21670)) 469565485 469598253 = 107 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 469565485 469598253).card = 107 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21670 469565485 469598253
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21670)) 469598253 469631021 = 96 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 469598253 469631021).card = 96 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21670 469598253 469631021
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 469499949 469565485).card = 229 := by
  simpa using combineTwinPrimeSegments (by decide : 469499949 ≤ 469532717)
    (by decide : 469532717 ≤ 469565485) block0 block1

theorem join_0_1 : (twinPrimeSegment 469565485 469631021).card = 203 := by
  simpa using combineTwinPrimeSegments (by decide : 469565485 ≤ 469598253)
    (by decide : 469598253 ≤ 469631021) block2 block3

theorem join_1_0 : (twinPrimeSegment 469499949 469631021).card = 432 := by
  simpa using combineTwinPrimeSegments (by decide : 469499949 ≤ 469565485)
    (by decide : 469565485 ≤ 469631021) join_0_0 join_0_1

theorem total : (twinPrimeSegment 469499949 469631021).card = 432 := join_1_0

end S223C14
end Sude.GeneratedTwinScan
