import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S124C15
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16187)) 262012973 262045741 = 148 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 262012973 262045741).card = 148 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16187 262012973 262045741
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16188)) 262045741 262078509 = 121 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 262045741 262078509).card = 121 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16188 262045741 262078509
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16189)) 262078509 262111277 = 140 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 262078509 262111277).card = 140 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16189 262078509 262111277
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16190)) 262111277 262144045 = 132 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 262111277 262144045).card = 132 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16190 262111277 262144045
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 262012973 262078509).card = 269 := by
  simpa using combineTwinPrimeSegments (by decide : 262012973 ≤ 262045741)
    (by decide : 262045741 ≤ 262078509) block0 block1

theorem join_0_1 : (twinPrimeSegment 262078509 262144045).card = 272 := by
  simpa using combineTwinPrimeSegments (by decide : 262078509 ≤ 262111277)
    (by decide : 262111277 ≤ 262144045) block2 block3

theorem join_1_0 : (twinPrimeSegment 262012973 262144045).card = 541 := by
  simpa using combineTwinPrimeSegments (by decide : 262012973 ≤ 262078509)
    (by decide : 262078509 ≤ 262144045) join_0_0 join_0_1

theorem total : (twinPrimeSegment 262012973 262144045).card = 541 := join_1_0

end S124C15
end Sude.GeneratedTwinScan
