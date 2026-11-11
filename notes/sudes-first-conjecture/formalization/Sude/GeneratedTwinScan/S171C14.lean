import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S171C14
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18986)) 360448045 360480813 = 138 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 360448045 360480813).card = 138 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18986 360448045 360480813
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18987)) 360480813 360513581 = 116 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 360480813 360513581).card = 116 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18987 360480813 360513581
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18988)) 360513581 360546349 = 114 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 360513581 360546349).card = 114 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18988 360513581 360546349
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18988)) 360546349 360579117 = 110 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 360546349 360579117).card = 110 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18988 360546349 360579117
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 360448045 360513581).card = 254 := by
  simpa using combineTwinPrimeSegments (by decide : 360448045 ≤ 360480813)
    (by decide : 360480813 ≤ 360513581) block0 block1

theorem join_0_1 : (twinPrimeSegment 360513581 360579117).card = 224 := by
  simpa using combineTwinPrimeSegments (by decide : 360513581 ≤ 360546349)
    (by decide : 360546349 ≤ 360579117) block2 block3

theorem join_1_0 : (twinPrimeSegment 360448045 360579117).card = 478 := by
  simpa using combineTwinPrimeSegments (by decide : 360448045 ≤ 360513581)
    (by decide : 360513581 ≤ 360579117) join_0_0 join_0_1

theorem total : (twinPrimeSegment 360448045 360579117).card = 478 := join_1_0

end S171C14
end Sude.GeneratedTwinScan
