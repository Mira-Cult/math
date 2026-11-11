import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S216C00
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21284)) 452984877 453017645 = 105 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 452984877 453017645).card = 105 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21284 452984877 453017645
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21284)) 453017645 453050413 = 106 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 453017645 453050413).card = 106 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21284 453017645 453050413
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21285)) 453050413 453083181 = 115 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 453050413 453083181).card = 115 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21285 453050413 453083181
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21286)) 453083181 453115949 = 109 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 453083181 453115949).card = 109 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21286 453083181 453115949
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 452984877 453050413).card = 211 := by
  simpa using combineTwinPrimeSegments (by decide : 452984877 ≤ 453017645)
    (by decide : 453017645 ≤ 453050413) block0 block1

theorem join_0_1 : (twinPrimeSegment 453050413 453115949).card = 224 := by
  simpa using combineTwinPrimeSegments (by decide : 453050413 ≤ 453083181)
    (by decide : 453083181 ≤ 453115949) block2 block3

theorem join_1_0 : (twinPrimeSegment 452984877 453115949).card = 435 := by
  simpa using combineTwinPrimeSegments (by decide : 452984877 ≤ 453050413)
    (by decide : 453050413 ≤ 453115949) join_0_0 join_0_1

theorem total : (twinPrimeSegment 452984877 453115949).card = 435 := join_1_0

end S216C00
end Sude.GeneratedTwinScan
