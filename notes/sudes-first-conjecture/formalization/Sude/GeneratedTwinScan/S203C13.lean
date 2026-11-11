import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S203C13
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20675)) 427425837 427458605 = 113 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 427425837 427458605).card = 113 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20675 427425837 427458605
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20675)) 427458605 427491373 = 106 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 427458605 427491373).card = 106 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20675 427458605 427491373
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20676)) 427491373 427524141 = 101 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 427491373 427524141).card = 101 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20676 427491373 427524141
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20677)) 427524141 427556909 = 115 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 427524141 427556909).card = 115 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20677 427524141 427556909
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 427425837 427491373).card = 219 := by
  simpa using combineTwinPrimeSegments (by decide : 427425837 ≤ 427458605)
    (by decide : 427458605 ≤ 427491373) block0 block1

theorem join_0_1 : (twinPrimeSegment 427491373 427556909).card = 216 := by
  simpa using combineTwinPrimeSegments (by decide : 427491373 ≤ 427524141)
    (by decide : 427524141 ≤ 427556909) block2 block3

theorem join_1_0 : (twinPrimeSegment 427425837 427556909).card = 435 := by
  simpa using combineTwinPrimeSegments (by decide : 427425837 ≤ 427491373)
    (by decide : 427491373 ≤ 427556909) join_0_0 join_0_1

theorem total : (twinPrimeSegment 427425837 427556909).card = 435 := join_1_0

end S203C13
end Sude.GeneratedTwinScan
