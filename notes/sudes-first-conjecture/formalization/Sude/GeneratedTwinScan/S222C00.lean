import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S222C00
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21577)) 465567789 465600557 = 139 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 465567789 465600557).card = 139 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21577 465567789 465600557
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21578)) 465600557 465633325 = 113 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 465600557 465633325).card = 113 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21578 465600557 465633325
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21579)) 465633325 465666093 = 94 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 465633325 465666093).card = 94 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21579 465633325 465666093
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21580)) 465666093 465698861 = 113 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 465666093 465698861).card = 113 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21580 465666093 465698861
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 465567789 465633325).card = 252 := by
  simpa using combineTwinPrimeSegments (by decide : 465567789 ≤ 465600557)
    (by decide : 465600557 ≤ 465633325) block0 block1

theorem join_0_1 : (twinPrimeSegment 465633325 465698861).card = 207 := by
  simpa using combineTwinPrimeSegments (by decide : 465633325 ≤ 465666093)
    (by decide : 465666093 ≤ 465698861) block2 block3

theorem join_1_0 : (twinPrimeSegment 465567789 465698861).card = 459 := by
  simpa using combineTwinPrimeSegments (by decide : 465567789 ≤ 465633325)
    (by decide : 465633325 ≤ 465698861) join_0_0 join_0_1

theorem total : (twinPrimeSegment 465567789 465698861).card = 459 := join_1_0

end S222C00
end Sude.GeneratedTwinScan
