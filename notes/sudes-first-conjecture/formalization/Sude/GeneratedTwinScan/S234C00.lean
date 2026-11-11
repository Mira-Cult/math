import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S234C00
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22153)) 490733613 490766381 = 109 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 490733613 490766381).card = 109 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22153 490733613 490766381
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22153)) 490766381 490799149 = 111 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 490766381 490799149).card = 111 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22153 490766381 490799149
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22154)) 490799149 490831917 = 99 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 490799149 490831917).card = 99 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22154 490799149 490831917
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22155)) 490831917 490864685 = 109 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 490831917 490864685).card = 109 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22155 490831917 490864685
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 490733613 490799149).card = 220 := by
  simpa using combineTwinPrimeSegments (by decide : 490733613 ≤ 490766381)
    (by decide : 490766381 ≤ 490799149) block0 block1

theorem join_0_1 : (twinPrimeSegment 490799149 490864685).card = 208 := by
  simpa using combineTwinPrimeSegments (by decide : 490799149 ≤ 490831917)
    (by decide : 490831917 ≤ 490864685) block2 block3

theorem join_1_0 : (twinPrimeSegment 490733613 490864685).card = 428 := by
  simpa using combineTwinPrimeSegments (by decide : 490733613 ≤ 490799149)
    (by decide : 490799149 ≤ 490864685) join_0_0 join_0_1

theorem total : (twinPrimeSegment 490733613 490864685).card = 428 := join_1_0

end S234C00
end Sude.GeneratedTwinScan
