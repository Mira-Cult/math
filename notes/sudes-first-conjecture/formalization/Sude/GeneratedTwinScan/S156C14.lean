import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S156C14
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18139)) 328990765 329023533 = 105 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 328990765 329023533).card = 105 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18139 328990765 329023533
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18139)) 329023533 329056301 = 109 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 329023533 329056301).card = 109 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18139 329023533 329056301
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18140)) 329056301 329089069 = 116 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 329056301 329089069).card = 116 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18140 329056301 329089069
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18141)) 329089069 329121837 = 131 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 329089069 329121837).card = 131 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18141 329089069 329121837
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 328990765 329056301).card = 214 := by
  simpa using combineTwinPrimeSegments (by decide : 328990765 ≤ 329023533)
    (by decide : 329023533 ≤ 329056301) block0 block1

theorem join_0_1 : (twinPrimeSegment 329056301 329121837).card = 247 := by
  simpa using combineTwinPrimeSegments (by decide : 329056301 ≤ 329089069)
    (by decide : 329089069 ≤ 329121837) block2 block3

theorem join_1_0 : (twinPrimeSegment 328990765 329121837).card = 461 := by
  simpa using combineTwinPrimeSegments (by decide : 328990765 ≤ 329056301)
    (by decide : 329056301 ≤ 329121837) join_0_0 join_0_1

theorem total : (twinPrimeSegment 328990765 329121837).card = 461 := join_1_0

end S156C14
end Sude.GeneratedTwinScan
