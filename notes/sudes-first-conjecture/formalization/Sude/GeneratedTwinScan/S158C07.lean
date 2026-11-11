import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S158C07
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18229)) 332267565 332300333 = 100 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 332267565 332300333).card = 100 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18229 332267565 332300333
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18230)) 332300333 332333101 = 111 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 332300333 332333101).card = 111 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18230 332300333 332333101
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18230)) 332333101 332365869 = 85 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 332333101 332365869).card = 85 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18230 332333101 332365869
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18231)) 332365869 332398637 = 117 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 332365869 332398637).card = 117 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18231 332365869 332398637
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 332267565 332333101).card = 211 := by
  simpa using combineTwinPrimeSegments (by decide : 332267565 ≤ 332300333)
    (by decide : 332300333 ≤ 332333101) block0 block1

theorem join_0_1 : (twinPrimeSegment 332333101 332398637).card = 202 := by
  simpa using combineTwinPrimeSegments (by decide : 332333101 ≤ 332365869)
    (by decide : 332365869 ≤ 332398637) block2 block3

theorem join_1_0 : (twinPrimeSegment 332267565 332398637).card = 413 := by
  simpa using combineTwinPrimeSegments (by decide : 332267565 ≤ 332333101)
    (by decide : 332333101 ≤ 332398637) join_0_0 join_0_1

theorem total : (twinPrimeSegment 332267565 332398637).card = 413 := join_1_0

end S158C07
end Sude.GeneratedTwinScan
