import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S099C14
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14473)) 209453101 209485869 = 122 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 209453101 209485869).card = 122 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14473 209453101 209485869
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14474)) 209485869 209518637 = 132 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 209485869 209518637).card = 132 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14474 209485869 209518637
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14475)) 209518637 209551405 = 119 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 209518637 209551405).card = 119 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14475 209518637 209551405
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14477)) 209551405 209584173 = 127 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 209551405 209584173).card = 127 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14477 209551405 209584173
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 209453101 209518637).card = 254 := by
  simpa using combineTwinPrimeSegments (by decide : 209453101 ≤ 209485869)
    (by decide : 209485869 ≤ 209518637) block0 block1

theorem join_0_1 : (twinPrimeSegment 209518637 209584173).card = 246 := by
  simpa using combineTwinPrimeSegments (by decide : 209518637 ≤ 209551405)
    (by decide : 209551405 ≤ 209584173) block2 block3

theorem join_1_0 : (twinPrimeSegment 209453101 209584173).card = 500 := by
  simpa using combineTwinPrimeSegments (by decide : 209453101 ≤ 209518637)
    (by decide : 209518637 ≤ 209584173) join_0_0 join_0_1

theorem total : (twinPrimeSegment 209453101 209584173).card = 500 := join_1_0

end S099C14
end Sude.GeneratedTwinScan
