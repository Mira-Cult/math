import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S187C12
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19843)) 393740333 393773101 = 114 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 393740333 393773101).card = 114 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19843 393740333 393773101
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19844)) 393773101 393805869 = 129 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 393773101 393805869).card = 129 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19844 393773101 393805869
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19845)) 393805869 393838637 = 116 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 393805869 393838637).card = 116 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19845 393805869 393838637
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19846)) 393838637 393871405 = 104 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 393838637 393871405).card = 104 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19846 393838637 393871405
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 393740333 393805869).card = 243 := by
  simpa using combineTwinPrimeSegments (by decide : 393740333 ≤ 393773101)
    (by decide : 393773101 ≤ 393805869) block0 block1

theorem join_0_1 : (twinPrimeSegment 393805869 393871405).card = 220 := by
  simpa using combineTwinPrimeSegments (by decide : 393805869 ≤ 393838637)
    (by decide : 393838637 ≤ 393871405) block2 block3

theorem join_1_0 : (twinPrimeSegment 393740333 393871405).card = 463 := by
  simpa using combineTwinPrimeSegments (by decide : 393740333 ≤ 393805869)
    (by decide : 393805869 ≤ 393871405) join_0_0 join_0_1

theorem total : (twinPrimeSegment 393740333 393871405).card = 463 := join_1_0

end S187C12
end Sude.GeneratedTwinScan
