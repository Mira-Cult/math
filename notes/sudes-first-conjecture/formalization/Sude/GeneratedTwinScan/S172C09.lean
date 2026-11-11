import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S172C09
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19024)) 361889837 361922605 = 113 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 361889837 361922605).card = 113 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19024 361889837 361922605
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19025)) 361922605 361955373 = 114 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 361922605 361955373).card = 114 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19025 361922605 361955373
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19025)) 361955373 361988141 = 104 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 361955373 361988141).card = 104 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19025 361955373 361988141
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19026)) 361988141 362020909 = 99 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 361988141 362020909).card = 99 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19026 361988141 362020909
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 361889837 361955373).card = 227 := by
  simpa using combineTwinPrimeSegments (by decide : 361889837 ≤ 361922605)
    (by decide : 361922605 ≤ 361955373) block0 block1

theorem join_0_1 : (twinPrimeSegment 361955373 362020909).card = 203 := by
  simpa using combineTwinPrimeSegments (by decide : 361955373 ≤ 361988141)
    (by decide : 361988141 ≤ 362020909) block2 block3

theorem join_1_0 : (twinPrimeSegment 361889837 362020909).card = 430 := by
  simpa using combineTwinPrimeSegments (by decide : 361889837 ≤ 361955373)
    (by decide : 361955373 ≤ 362020909) join_0_0 join_0_1

theorem total : (twinPrimeSegment 361889837 362020909).card = 430 := join_1_0

end S172C09
end Sude.GeneratedTwinScan
