import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S185C03
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19707)) 388366381 388399149 = 127 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 388366381 388399149).card = 127 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19707 388366381 388399149
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19708)) 388399149 388431917 = 99 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 388399149 388431917).card = 99 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19708 388399149 388431917
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19709)) 388431917 388464685 = 110 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 388431917 388464685).card = 110 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19709 388431917 388464685
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19710)) 388464685 388497453 = 111 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 388464685 388497453).card = 111 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19710 388464685 388497453
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 388366381 388431917).card = 226 := by
  simpa using combineTwinPrimeSegments (by decide : 388366381 ≤ 388399149)
    (by decide : 388399149 ≤ 388431917) block0 block1

theorem join_0_1 : (twinPrimeSegment 388431917 388497453).card = 221 := by
  simpa using combineTwinPrimeSegments (by decide : 388431917 ≤ 388464685)
    (by decide : 388464685 ≤ 388497453) block2 block3

theorem join_1_0 : (twinPrimeSegment 388366381 388497453).card = 447 := by
  simpa using combineTwinPrimeSegments (by decide : 388366381 ≤ 388431917)
    (by decide : 388431917 ≤ 388497453) join_0_0 join_0_1

theorem total : (twinPrimeSegment 388366381 388497453).card = 447 := join_1_0

end S185C03
end Sude.GeneratedTwinScan
