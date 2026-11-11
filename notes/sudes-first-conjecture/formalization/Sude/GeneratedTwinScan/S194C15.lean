import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S194C15
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20219)) 408813613 408846381 = 116 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 408813613 408846381).card = 116 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20219 408813613 408846381
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20220)) 408846381 408879149 = 93 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 408846381 408879149).card = 93 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20220 408846381 408879149
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20221)) 408879149 408911917 = 120 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 408879149 408911917).card = 120 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20221 408879149 408911917
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20222)) 408911917 408944685 = 121 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 408911917 408944685).card = 121 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20222 408911917 408944685
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 408813613 408879149).card = 209 := by
  simpa using combineTwinPrimeSegments (by decide : 408813613 ≤ 408846381)
    (by decide : 408846381 ≤ 408879149) block0 block1

theorem join_0_1 : (twinPrimeSegment 408879149 408944685).card = 241 := by
  simpa using combineTwinPrimeSegments (by decide : 408879149 ≤ 408911917)
    (by decide : 408911917 ≤ 408944685) block2 block3

theorem join_1_0 : (twinPrimeSegment 408813613 408944685).card = 450 := by
  simpa using combineTwinPrimeSegments (by decide : 408813613 ≤ 408879149)
    (by decide : 408879149 ≤ 408944685) join_0_0 join_0_1

theorem total : (twinPrimeSegment 408813613 408944685).card = 450 := join_1_0

end S194C15
end Sude.GeneratedTwinScan
