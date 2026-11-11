import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S244C10
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22650)) 513015853 513048621 = 118 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 513015853 513048621).card = 118 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22650 513015853 513048621
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22651)) 513048621 513081389 = 119 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 513048621 513081389).card = 119 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22651 513048621 513081389
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22652)) 513081389 513114157 = 104 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 513081389 513114157).card = 104 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22652 513081389 513114157
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22652)) 513114157 513146925 = 114 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 513114157 513146925).card = 114 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22652 513114157 513146925
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 513015853 513081389).card = 237 := by
  simpa using combineTwinPrimeSegments (by decide : 513015853 ≤ 513048621)
    (by decide : 513048621 ≤ 513081389) block0 block1

theorem join_0_1 : (twinPrimeSegment 513081389 513146925).card = 218 := by
  simpa using combineTwinPrimeSegments (by decide : 513081389 ≤ 513114157)
    (by decide : 513114157 ≤ 513146925) block2 block3

theorem join_1_0 : (twinPrimeSegment 513015853 513146925).card = 455 := by
  simpa using combineTwinPrimeSegments (by decide : 513015853 ≤ 513081389)
    (by decide : 513081389 ≤ 513146925) join_0_0 join_0_1

theorem total : (twinPrimeSegment 513015853 513146925).card = 455 := join_1_0

end S244C10
end Sude.GeneratedTwinScan
