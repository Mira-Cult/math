import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S078C12
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 12852)) 165150765 165183533 = 131 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 165150765 165183533).card = 131 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 12852 165150765 165183533
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 12853)) 165183533 165216301 = 120 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 165183533 165216301).card = 120 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 12853 165183533 165216301
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 12854)) 165216301 165249069 = 115 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 165216301 165249069).card = 115 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 12854 165216301 165249069
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 12856)) 165249069 165281837 = 145 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 165249069 165281837).card = 145 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 12856 165249069 165281837
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 165150765 165216301).card = 251 := by
  simpa using combineTwinPrimeSegments (by decide : 165150765 ≤ 165183533)
    (by decide : 165183533 ≤ 165216301) block0 block1

theorem join_0_1 : (twinPrimeSegment 165216301 165281837).card = 260 := by
  simpa using combineTwinPrimeSegments (by decide : 165216301 ≤ 165249069)
    (by decide : 165249069 ≤ 165281837) block2 block3

theorem join_1_0 : (twinPrimeSegment 165150765 165281837).card = 511 := by
  simpa using combineTwinPrimeSegments (by decide : 165150765 ≤ 165216301)
    (by decide : 165216301 ≤ 165281837) join_0_0 join_0_1

theorem total : (twinPrimeSegment 165150765 165281837).card = 511 := join_1_0

end S078C12
end Sude.GeneratedTwinScan
