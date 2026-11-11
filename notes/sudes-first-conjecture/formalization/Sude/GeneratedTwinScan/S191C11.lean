import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S191C11
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20050)) 401997869 402030637 = 104 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 401997869 402030637).card = 104 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20050 401997869 402030637
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20051)) 402030637 402063405 = 125 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 402030637 402063405).card = 125 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20051 402030637 402063405
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20052)) 402063405 402096173 = 124 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 402063405 402096173).card = 124 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20052 402063405 402096173
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20053)) 402096173 402128941 = 112 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 402096173 402128941).card = 112 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20053 402096173 402128941
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 401997869 402063405).card = 229 := by
  simpa using combineTwinPrimeSegments (by decide : 401997869 ≤ 402030637)
    (by decide : 402030637 ≤ 402063405) block0 block1

theorem join_0_1 : (twinPrimeSegment 402063405 402128941).card = 236 := by
  simpa using combineTwinPrimeSegments (by decide : 402063405 ≤ 402096173)
    (by decide : 402096173 ≤ 402128941) block2 block3

theorem join_1_0 : (twinPrimeSegment 401997869 402128941).card = 465 := by
  simpa using combineTwinPrimeSegments (by decide : 401997869 ≤ 402063405)
    (by decide : 402063405 ≤ 402128941) join_0_0 join_0_1

theorem total : (twinPrimeSegment 401997869 402128941).card = 465 := join_1_0

end S191C11
end Sude.GeneratedTwinScan
