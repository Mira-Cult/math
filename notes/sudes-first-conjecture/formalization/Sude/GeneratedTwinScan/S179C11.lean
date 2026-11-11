import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S179C11
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19413)) 376832045 376864813 = 102 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 376832045 376864813).card = 102 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19413 376832045 376864813
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19413)) 376864813 376897581 = 111 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 376864813 376897581).card = 111 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19413 376864813 376897581
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19414)) 376897581 376930349 = 107 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 376897581 376930349).card = 107 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19414 376897581 376930349
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19415)) 376930349 376963117 = 116 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 376930349 376963117).card = 116 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19415 376930349 376963117
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 376832045 376897581).card = 213 := by
  simpa using combineTwinPrimeSegments (by decide : 376832045 ≤ 376864813)
    (by decide : 376864813 ≤ 376897581) block0 block1

theorem join_0_1 : (twinPrimeSegment 376897581 376963117).card = 223 := by
  simpa using combineTwinPrimeSegments (by decide : 376897581 ≤ 376930349)
    (by decide : 376930349 ≤ 376963117) block2 block3

theorem join_1_0 : (twinPrimeSegment 376832045 376963117).card = 436 := by
  simpa using combineTwinPrimeSegments (by decide : 376832045 ≤ 376897581)
    (by decide : 376897581 ≤ 376963117) join_0_0 join_0_1

theorem total : (twinPrimeSegment 376832045 376963117).card = 436 := join_1_0

end S179C11
end Sude.GeneratedTwinScan
