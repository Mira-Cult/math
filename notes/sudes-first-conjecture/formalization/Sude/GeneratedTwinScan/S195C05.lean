import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S195C05
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20239)) 409600045 409632813 = 104 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 409600045 409632813).card = 104 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20239 409600045 409632813
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20240)) 409632813 409665581 = 118 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 409632813 409665581).card = 118 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20240 409632813 409665581
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20241)) 409665581 409698349 = 118 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 409665581 409698349).card = 118 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20241 409665581 409698349
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20241)) 409698349 409731117 = 113 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 409698349 409731117).card = 113 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20241 409698349 409731117
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 409600045 409665581).card = 222 := by
  simpa using combineTwinPrimeSegments (by decide : 409600045 ≤ 409632813)
    (by decide : 409632813 ≤ 409665581) block0 block1

theorem join_0_1 : (twinPrimeSegment 409665581 409731117).card = 231 := by
  simpa using combineTwinPrimeSegments (by decide : 409665581 ≤ 409698349)
    (by decide : 409698349 ≤ 409731117) block2 block3

theorem join_1_0 : (twinPrimeSegment 409600045 409731117).card = 453 := by
  simpa using combineTwinPrimeSegments (by decide : 409600045 ≤ 409665581)
    (by decide : 409665581 ≤ 409731117) join_0_0 join_0_1

theorem total : (twinPrimeSegment 409600045 409731117).card = 453 := join_1_0

end S195C05
end Sude.GeneratedTwinScan
