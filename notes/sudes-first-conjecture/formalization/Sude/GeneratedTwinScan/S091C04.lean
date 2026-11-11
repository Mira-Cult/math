import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S091C04
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13834)) 191365165 191397933 = 113 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 191365165 191397933).card = 113 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13834 191365165 191397933
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13835)) 191397933 191430701 = 119 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 191397933 191430701).card = 119 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13835 191397933 191430701
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13837)) 191430701 191463469 = 113 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 191430701 191463469).card = 113 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13837 191430701 191463469
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13838)) 191463469 191496237 = 116 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 191463469 191496237).card = 116 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13838 191463469 191496237
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 191365165 191430701).card = 232 := by
  simpa using combineTwinPrimeSegments (by decide : 191365165 ≤ 191397933)
    (by decide : 191397933 ≤ 191430701) block0 block1

theorem join_0_1 : (twinPrimeSegment 191430701 191496237).card = 229 := by
  simpa using combineTwinPrimeSegments (by decide : 191430701 ≤ 191463469)
    (by decide : 191463469 ≤ 191496237) block2 block3

theorem join_1_0 : (twinPrimeSegment 191365165 191496237).card = 461 := by
  simpa using combineTwinPrimeSegments (by decide : 191365165 ≤ 191430701)
    (by decide : 191430701 ≤ 191496237) join_0_0 join_0_1

theorem total : (twinPrimeSegment 191365165 191496237).card = 461 := join_1_0

end S091C04
end Sude.GeneratedTwinScan
