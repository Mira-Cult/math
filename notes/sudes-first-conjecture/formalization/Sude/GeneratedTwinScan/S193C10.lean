import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S193C10
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20151)) 406061101 406093869 = 103 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 406061101 406093869).card = 103 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20151 406061101 406093869
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20152)) 406093869 406126637 = 97 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 406093869 406126637).card = 97 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20152 406093869 406126637
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20153)) 406126637 406159405 = 123 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 406126637 406159405).card = 123 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20153 406126637 406159405
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20154)) 406159405 406192173 = 114 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 406159405 406192173).card = 114 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20154 406159405 406192173
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 406061101 406126637).card = 200 := by
  simpa using combineTwinPrimeSegments (by decide : 406061101 ≤ 406093869)
    (by decide : 406093869 ≤ 406126637) block0 block1

theorem join_0_1 : (twinPrimeSegment 406126637 406192173).card = 237 := by
  simpa using combineTwinPrimeSegments (by decide : 406126637 ≤ 406159405)
    (by decide : 406159405 ≤ 406192173) block2 block3

theorem join_1_0 : (twinPrimeSegment 406061101 406192173).card = 437 := by
  simpa using combineTwinPrimeSegments (by decide : 406061101 ≤ 406126637)
    (by decide : 406126637 ≤ 406192173) join_0_0 join_0_1

theorem total : (twinPrimeSegment 406061101 406192173).card = 437 := join_1_0

end S193C10
end Sude.GeneratedTwinScan
