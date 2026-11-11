import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S107C01
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14985)) 224526381 224559149 = 114 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 224526381 224559149).card = 114 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14985 224526381 224559149
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14986)) 224559149 224591917 = 126 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 224559149 224591917).card = 126 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14986 224559149 224591917
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14987)) 224591917 224624685 = 116 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 224591917 224624685).card = 116 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14987 224591917 224624685
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14988)) 224624685 224657453 = 129 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 224624685 224657453).card = 129 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14988 224624685 224657453
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 224526381 224591917).card = 240 := by
  simpa using combineTwinPrimeSegments (by decide : 224526381 ≤ 224559149)
    (by decide : 224559149 ≤ 224591917) block0 block1

theorem join_0_1 : (twinPrimeSegment 224591917 224657453).card = 245 := by
  simpa using combineTwinPrimeSegments (by decide : 224591917 ≤ 224624685)
    (by decide : 224624685 ≤ 224657453) block2 block3

theorem join_1_0 : (twinPrimeSegment 224526381 224657453).card = 485 := by
  simpa using combineTwinPrimeSegments (by decide : 224526381 ≤ 224591917)
    (by decide : 224591917 ≤ 224657453) join_0_0 join_0_1

theorem total : (twinPrimeSegment 224526381 224657453).card = 485 := join_1_0

end S107C01
end Sude.GeneratedTwinScan
