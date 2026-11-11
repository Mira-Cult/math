import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S234C03
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22162)) 491126829 491159597 = 125 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 491126829 491159597).card = 125 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22162 491126829 491159597
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22162)) 491159597 491192365 = 114 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 491159597 491192365).card = 114 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22162 491159597 491192365
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22163)) 491192365 491225133 = 109 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 491192365 491225133).card = 109 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22163 491192365 491225133
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22164)) 491225133 491257901 = 99 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 491225133 491257901).card = 99 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22164 491225133 491257901
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 491126829 491192365).card = 239 := by
  simpa using combineTwinPrimeSegments (by decide : 491126829 ≤ 491159597)
    (by decide : 491159597 ≤ 491192365) block0 block1

theorem join_0_1 : (twinPrimeSegment 491192365 491257901).card = 208 := by
  simpa using combineTwinPrimeSegments (by decide : 491192365 ≤ 491225133)
    (by decide : 491225133 ≤ 491257901) block2 block3

theorem join_1_0 : (twinPrimeSegment 491126829 491257901).card = 447 := by
  simpa using combineTwinPrimeSegments (by decide : 491126829 ≤ 491192365)
    (by decide : 491192365 ≤ 491257901) join_0_0 join_0_1

theorem total : (twinPrimeSegment 491126829 491257901).card = 447 := join_1_0

end S234C03
end Sude.GeneratedTwinScan
