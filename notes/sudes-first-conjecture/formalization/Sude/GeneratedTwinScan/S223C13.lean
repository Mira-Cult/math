import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S223C13
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21665)) 469368877 469401645 = 107 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 469368877 469401645).card = 107 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21665 469368877 469401645
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21666)) 469401645 469434413 = 115 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 469401645 469434413).card = 115 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21666 469401645 469434413
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21667)) 469434413 469467181 = 106 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 469434413 469467181).card = 106 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21667 469434413 469467181
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21667)) 469467181 469499949 = 113 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 469467181 469499949).card = 113 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21667 469467181 469499949
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 469368877 469434413).card = 222 := by
  simpa using combineTwinPrimeSegments (by decide : 469368877 ≤ 469401645)
    (by decide : 469401645 ≤ 469434413) block0 block1

theorem join_0_1 : (twinPrimeSegment 469434413 469499949).card = 219 := by
  simpa using combineTwinPrimeSegments (by decide : 469434413 ≤ 469467181)
    (by decide : 469467181 ≤ 469499949) block2 block3

theorem join_1_0 : (twinPrimeSegment 469368877 469499949).card = 441 := by
  simpa using combineTwinPrimeSegments (by decide : 469368877 ≤ 469434413)
    (by decide : 469434413 ≤ 469499949) join_0_0 join_0_1

theorem total : (twinPrimeSegment 469368877 469499949).card = 441 := join_1_0

end S223C13
end Sude.GeneratedTwinScan
