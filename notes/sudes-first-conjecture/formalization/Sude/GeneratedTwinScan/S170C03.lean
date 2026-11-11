import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S170C03
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18892)) 356909101 356941869 = 89 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 356909101 356941869).card = 89 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18892 356909101 356941869
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18893)) 356941869 356974637 = 124 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 356941869 356974637).card = 124 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18893 356941869 356974637
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18894)) 356974637 357007405 = 101 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 356974637 357007405).card = 101 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18894 356974637 357007405
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18895)) 357007405 357040173 = 117 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 357007405 357040173).card = 117 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18895 357007405 357040173
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 356909101 356974637).card = 213 := by
  simpa using combineTwinPrimeSegments (by decide : 356909101 ≤ 356941869)
    (by decide : 356941869 ≤ 356974637) block0 block1

theorem join_0_1 : (twinPrimeSegment 356974637 357040173).card = 218 := by
  simpa using combineTwinPrimeSegments (by decide : 356974637 ≤ 357007405)
    (by decide : 357007405 ≤ 357040173) block2 block3

theorem join_1_0 : (twinPrimeSegment 356909101 357040173).card = 431 := by
  simpa using combineTwinPrimeSegments (by decide : 356909101 ≤ 356974637)
    (by decide : 356974637 ≤ 357040173) join_0_0 join_0_1

theorem total : (twinPrimeSegment 356909101 357040173).card = 431 := join_1_0

end S170C03
end Sude.GeneratedTwinScan
