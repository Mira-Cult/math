import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S085C15
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13425)) 180224045 180256813 = 109 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 180224045 180256813).card = 109 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13425 180224045 180256813
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13427)) 180256813 180289581 = 119 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 180256813 180289581).card = 119 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13427 180256813 180289581
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13428)) 180289581 180322349 = 118 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 180289581 180322349).card = 118 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13428 180289581 180322349
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13429)) 180322349 180355117 = 135 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 180322349 180355117).card = 135 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13429 180322349 180355117
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 180224045 180289581).card = 228 := by
  simpa using combineTwinPrimeSegments (by decide : 180224045 ≤ 180256813)
    (by decide : 180256813 ≤ 180289581) block0 block1

theorem join_0_1 : (twinPrimeSegment 180289581 180355117).card = 253 := by
  simpa using combineTwinPrimeSegments (by decide : 180289581 ≤ 180322349)
    (by decide : 180322349 ≤ 180355117) block2 block3

theorem join_1_0 : (twinPrimeSegment 180224045 180355117).card = 481 := by
  simpa using combineTwinPrimeSegments (by decide : 180224045 ≤ 180289581)
    (by decide : 180289581 ≤ 180355117) join_0_0 join_0_1

theorem total : (twinPrimeSegment 180224045 180355117).card = 481 := join_1_0

end S085C15
end Sude.GeneratedTwinScan
