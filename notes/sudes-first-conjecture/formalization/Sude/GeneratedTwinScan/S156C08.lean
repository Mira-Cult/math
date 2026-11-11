import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S156C08
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18117)) 328204333 328237101 = 113 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 328204333 328237101).card = 113 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18117 328204333 328237101
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18118)) 328237101 328269869 = 116 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 328237101 328269869).card = 116 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18118 328237101 328269869
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18119)) 328269869 328302637 = 111 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 328269869 328302637).card = 111 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18119 328269869 328302637
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18120)) 328302637 328335405 = 109 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 328302637 328335405).card = 109 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18120 328302637 328335405
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 328204333 328269869).card = 229 := by
  simpa using combineTwinPrimeSegments (by decide : 328204333 ≤ 328237101)
    (by decide : 328237101 ≤ 328269869) block0 block1

theorem join_0_1 : (twinPrimeSegment 328269869 328335405).card = 220 := by
  simpa using combineTwinPrimeSegments (by decide : 328269869 ≤ 328302637)
    (by decide : 328302637 ≤ 328335405) block2 block3

theorem join_1_0 : (twinPrimeSegment 328204333 328335405).card = 449 := by
  simpa using combineTwinPrimeSegments (by decide : 328204333 ≤ 328269869)
    (by decide : 328269869 ≤ 328335405) join_0_0 join_0_1

theorem total : (twinPrimeSegment 328204333 328335405).card = 449 := join_1_0

end S156C08
end Sude.GeneratedTwinScan
