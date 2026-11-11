import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S077C15
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 12785)) 163446829 163479597 = 126 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 163446829 163479597).card = 126 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 12785 163446829 163479597
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 12787)) 163479597 163512365 = 109 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 163479597 163512365).card = 109 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 12787 163479597 163512365
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 12788)) 163512365 163545133 = 117 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 163512365 163545133).card = 117 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 12788 163512365 163545133
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 12789)) 163545133 163577901 = 136 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 163545133 163577901).card = 136 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 12789 163545133 163577901
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 163446829 163512365).card = 235 := by
  simpa using combineTwinPrimeSegments (by decide : 163446829 ≤ 163479597)
    (by decide : 163479597 ≤ 163512365) block0 block1

theorem join_0_1 : (twinPrimeSegment 163512365 163577901).card = 253 := by
  simpa using combineTwinPrimeSegments (by decide : 163512365 ≤ 163545133)
    (by decide : 163545133 ≤ 163577901) block2 block3

theorem join_1_0 : (twinPrimeSegment 163446829 163577901).card = 488 := by
  simpa using combineTwinPrimeSegments (by decide : 163446829 ≤ 163512365)
    (by decide : 163512365 ≤ 163577901) join_0_0 join_0_1

theorem total : (twinPrimeSegment 163446829 163577901).card = 488 := join_1_0

end S077C15
end Sude.GeneratedTwinScan
