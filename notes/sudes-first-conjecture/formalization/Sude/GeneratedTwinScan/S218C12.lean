import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S218C12
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21419)) 458752045 458784813 = 103 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 458752045 458784813).card = 103 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21419 458752045 458784813
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21420)) 458784813 458817581 = 93 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 458784813 458817581).card = 93 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21420 458784813 458817581
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21420)) 458817581 458850349 = 109 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 458817581 458850349).card = 109 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21420 458817581 458850349
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21421)) 458850349 458883117 = 112 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 458850349 458883117).card = 112 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21421 458850349 458883117
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 458752045 458817581).card = 196 := by
  simpa using combineTwinPrimeSegments (by decide : 458752045 ≤ 458784813)
    (by decide : 458784813 ≤ 458817581) block0 block1

theorem join_0_1 : (twinPrimeSegment 458817581 458883117).card = 221 := by
  simpa using combineTwinPrimeSegments (by decide : 458817581 ≤ 458850349)
    (by decide : 458850349 ≤ 458883117) block2 block3

theorem join_1_0 : (twinPrimeSegment 458752045 458883117).card = 417 := by
  simpa using combineTwinPrimeSegments (by decide : 458752045 ≤ 458817581)
    (by decide : 458817581 ≤ 458883117) join_0_0 join_0_1

theorem total : (twinPrimeSegment 458752045 458883117).card = 417 := join_1_0

end S218C12
end Sude.GeneratedTwinScan
