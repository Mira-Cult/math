import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S243C15
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22618)) 511574061 511606829 = 116 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 511574061 511606829).card = 116 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22618 511574061 511606829
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22619)) 511606829 511639597 = 110 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 511606829 511639597).card = 110 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22619 511606829 511639597
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22620)) 511639597 511672365 = 107 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 511639597 511672365).card = 107 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22620 511639597 511672365
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22620)) 511672365 511705133 = 102 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 511672365 511705133).card = 102 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22620 511672365 511705133
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 511574061 511639597).card = 226 := by
  simpa using combineTwinPrimeSegments (by decide : 511574061 ≤ 511606829)
    (by decide : 511606829 ≤ 511639597) block0 block1

theorem join_0_1 : (twinPrimeSegment 511639597 511705133).card = 209 := by
  simpa using combineTwinPrimeSegments (by decide : 511639597 ≤ 511672365)
    (by decide : 511672365 ≤ 511705133) block2 block3

theorem join_1_0 : (twinPrimeSegment 511574061 511705133).card = 435 := by
  simpa using combineTwinPrimeSegments (by decide : 511574061 ≤ 511639597)
    (by decide : 511639597 ≤ 511705133) join_0_0 join_0_1

theorem total : (twinPrimeSegment 511574061 511705133).card = 435 := join_1_0

end S243C15
end Sude.GeneratedTwinScan
