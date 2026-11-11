import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S092C04
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13910)) 193462317 193495085 = 121 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 193462317 193495085).card = 121 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13910 193462317 193495085
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13911)) 193495085 193527853 = 117 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 193495085 193527853).card = 117 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13911 193495085 193527853
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13912)) 193527853 193560621 = 134 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 193527853 193560621).card = 134 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13912 193527853 193560621
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13913)) 193560621 193593389 = 129 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 193560621 193593389).card = 129 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13913 193560621 193593389
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 193462317 193527853).card = 238 := by
  simpa using combineTwinPrimeSegments (by decide : 193462317 ≤ 193495085)
    (by decide : 193495085 ≤ 193527853) block0 block1

theorem join_0_1 : (twinPrimeSegment 193527853 193593389).card = 263 := by
  simpa using combineTwinPrimeSegments (by decide : 193527853 ≤ 193560621)
    (by decide : 193560621 ≤ 193593389) block2 block3

theorem join_1_0 : (twinPrimeSegment 193462317 193593389).card = 501 := by
  simpa using combineTwinPrimeSegments (by decide : 193462317 ≤ 193527853)
    (by decide : 193527853 ≤ 193593389) join_0_0 join_0_1

theorem total : (twinPrimeSegment 193462317 193593389).card = 501 := join_1_0

end S092C04
end Sude.GeneratedTwinScan
