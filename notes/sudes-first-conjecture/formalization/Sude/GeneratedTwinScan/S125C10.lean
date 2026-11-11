import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S125C10
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16232)) 263454765 263487533 = 115 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 263454765 263487533).card = 115 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16232 263454765 263487533
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16233)) 263487533 263520301 = 130 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 263487533 263520301).card = 130 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16233 263487533 263520301
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16234)) 263520301 263553069 = 117 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 263520301 263553069).card = 117 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16234 263520301 263553069
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16235)) 263553069 263585837 = 107 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 263553069 263585837).card = 107 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16235 263553069 263585837
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 263454765 263520301).card = 245 := by
  simpa using combineTwinPrimeSegments (by decide : 263454765 ≤ 263487533)
    (by decide : 263487533 ≤ 263520301) block0 block1

theorem join_0_1 : (twinPrimeSegment 263520301 263585837).card = 224 := by
  simpa using combineTwinPrimeSegments (by decide : 263520301 ≤ 263553069)
    (by decide : 263553069 ≤ 263585837) block2 block3

theorem join_1_0 : (twinPrimeSegment 263454765 263585837).card = 469 := by
  simpa using combineTwinPrimeSegments (by decide : 263454765 ≤ 263520301)
    (by decide : 263520301 ≤ 263585837) join_0_0 join_0_1

theorem total : (twinPrimeSegment 263454765 263585837).card = 469 := join_1_0

end S125C10
end Sude.GeneratedTwinScan
