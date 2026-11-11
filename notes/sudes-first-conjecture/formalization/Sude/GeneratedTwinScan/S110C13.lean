import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S110C13
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15245)) 232390701 232423469 = 119 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 232390701 232423469).card = 119 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15245 232390701 232423469
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15246)) 232423469 232456237 = 117 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 232423469 232456237).card = 117 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15246 232423469 232456237
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15247)) 232456237 232489005 = 123 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 232456237 232489005).card = 123 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15247 232456237 232489005
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15248)) 232489005 232521773 = 109 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 232489005 232521773).card = 109 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15248 232489005 232521773
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 232390701 232456237).card = 236 := by
  simpa using combineTwinPrimeSegments (by decide : 232390701 ≤ 232423469)
    (by decide : 232423469 ≤ 232456237) block0 block1

theorem join_0_1 : (twinPrimeSegment 232456237 232521773).card = 232 := by
  simpa using combineTwinPrimeSegments (by decide : 232456237 ≤ 232489005)
    (by decide : 232489005 ≤ 232521773) block2 block3

theorem join_1_0 : (twinPrimeSegment 232390701 232521773).card = 468 := by
  simpa using combineTwinPrimeSegments (by decide : 232390701 ≤ 232456237)
    (by decide : 232456237 ≤ 232521773) join_0_0 join_0_1

theorem total : (twinPrimeSegment 232390701 232521773).card = 468 := join_1_0

end S110C13
end Sude.GeneratedTwinScan
