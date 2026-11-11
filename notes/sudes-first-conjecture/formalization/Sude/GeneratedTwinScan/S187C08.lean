import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S187C08
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19830)) 393216045 393248813 = 93 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 393216045 393248813).card = 93 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19830 393216045 393248813
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19831)) 393248813 393281581 = 109 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 393248813 393281581).card = 109 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19831 393248813 393281581
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19832)) 393281581 393314349 = 104 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 393281581 393314349).card = 104 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19832 393281581 393314349
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19832)) 393314349 393347117 = 105 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 393314349 393347117).card = 105 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19832 393314349 393347117
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 393216045 393281581).card = 202 := by
  simpa using combineTwinPrimeSegments (by decide : 393216045 ≤ 393248813)
    (by decide : 393248813 ≤ 393281581) block0 block1

theorem join_0_1 : (twinPrimeSegment 393281581 393347117).card = 209 := by
  simpa using combineTwinPrimeSegments (by decide : 393281581 ≤ 393314349)
    (by decide : 393314349 ≤ 393347117) block2 block3

theorem join_1_0 : (twinPrimeSegment 393216045 393347117).card = 411 := by
  simpa using combineTwinPrimeSegments (by decide : 393216045 ≤ 393281581)
    (by decide : 393281581 ≤ 393347117) join_0_0 join_0_1

theorem total : (twinPrimeSegment 393216045 393347117).card = 411 := join_1_0

end S187C08
end Sude.GeneratedTwinScan
