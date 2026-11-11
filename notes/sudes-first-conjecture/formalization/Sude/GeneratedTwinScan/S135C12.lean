import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S135C12
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16873)) 284688429 284721197 = 123 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 284688429 284721197).card = 123 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16873 284688429 284721197
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16874)) 284721197 284753965 = 112 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 284721197 284753965).card = 112 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16874 284721197 284753965
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16875)) 284753965 284786733 = 117 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 284753965 284786733).card = 117 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16875 284753965 284786733
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16876)) 284786733 284819501 = 128 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 284786733 284819501).card = 128 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16876 284786733 284819501
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 284688429 284753965).card = 235 := by
  simpa using combineTwinPrimeSegments (by decide : 284688429 ≤ 284721197)
    (by decide : 284721197 ≤ 284753965) block0 block1

theorem join_0_1 : (twinPrimeSegment 284753965 284819501).card = 245 := by
  simpa using combineTwinPrimeSegments (by decide : 284753965 ≤ 284786733)
    (by decide : 284786733 ≤ 284819501) block2 block3

theorem join_1_0 : (twinPrimeSegment 284688429 284819501).card = 480 := by
  simpa using combineTwinPrimeSegments (by decide : 284688429 ≤ 284753965)
    (by decide : 284753965 ≤ 284819501) join_0_0 join_0_1

theorem total : (twinPrimeSegment 284688429 284819501).card = 480 := join_1_0

end S135C12
end Sude.GeneratedTwinScan
