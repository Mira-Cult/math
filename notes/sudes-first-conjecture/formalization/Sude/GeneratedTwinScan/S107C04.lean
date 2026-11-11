import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S107C04
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14998)) 224919597 224952365 = 132 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 224919597 224952365).card = 132 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14998 224919597 224952365
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14999)) 224952365 224985133 = 135 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 224952365 224985133).card = 135 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14999 224952365 224985133
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15000)) 224985133 225017901 = 107 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 224985133 225017901).card = 107 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15000 224985133 225017901
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15001)) 225017901 225050669 = 109 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 225017901 225050669).card = 109 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15001 225017901 225050669
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 224919597 224985133).card = 267 := by
  simpa using combineTwinPrimeSegments (by decide : 224919597 ≤ 224952365)
    (by decide : 224952365 ≤ 224985133) block0 block1

theorem join_0_1 : (twinPrimeSegment 224985133 225050669).card = 216 := by
  simpa using combineTwinPrimeSegments (by decide : 224985133 ≤ 225017901)
    (by decide : 225017901 ≤ 225050669) block2 block3

theorem join_1_0 : (twinPrimeSegment 224919597 225050669).card = 483 := by
  simpa using combineTwinPrimeSegments (by decide : 224919597 ≤ 224985133)
    (by decide : 224985133 ≤ 225050669) join_0_0 join_0_1

theorem total : (twinPrimeSegment 224919597 225050669).card = 483 := join_1_0

end S107C04
end Sude.GeneratedTwinScan
