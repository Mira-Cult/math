import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S205C01
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20738)) 430047277 430080045 = 112 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 430047277 430080045).card = 112 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20738 430047277 430080045
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20739)) 430080045 430112813 = 106 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 430080045 430112813).card = 106 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20739 430080045 430112813
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20739)) 430112813 430145581 = 99 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 430112813 430145581).card = 99 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20739 430112813 430145581
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20740)) 430145581 430178349 = 98 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 430145581 430178349).card = 98 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20740 430145581 430178349
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 430047277 430112813).card = 218 := by
  simpa using combineTwinPrimeSegments (by decide : 430047277 ≤ 430080045)
    (by decide : 430080045 ≤ 430112813) block0 block1

theorem join_0_1 : (twinPrimeSegment 430112813 430178349).card = 197 := by
  simpa using combineTwinPrimeSegments (by decide : 430112813 ≤ 430145581)
    (by decide : 430145581 ≤ 430178349) block2 block3

theorem join_1_0 : (twinPrimeSegment 430047277 430178349).card = 415 := by
  simpa using combineTwinPrimeSegments (by decide : 430047277 ≤ 430112813)
    (by decide : 430112813 ≤ 430178349) join_0_0 join_0_1

theorem total : (twinPrimeSegment 430047277 430178349).card = 415 := join_1_0

end S205C01
end Sude.GeneratedTwinScan
