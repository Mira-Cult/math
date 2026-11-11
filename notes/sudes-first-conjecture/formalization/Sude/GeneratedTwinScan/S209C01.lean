import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S209C01
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20939)) 438435885 438468653 = 135 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 438435885 438468653).card = 135 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20939 438435885 438468653
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20940)) 438468653 438501421 = 92 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 438468653 438501421).card = 92 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20940 438468653 438501421
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20941)) 438501421 438534189 = 124 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 438501421 438534189).card = 124 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20941 438501421 438534189
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20941)) 438534189 438566957 = 107 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 438534189 438566957).card = 107 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20941 438534189 438566957
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 438435885 438501421).card = 227 := by
  simpa using combineTwinPrimeSegments (by decide : 438435885 ≤ 438468653)
    (by decide : 438468653 ≤ 438501421) block0 block1

theorem join_0_1 : (twinPrimeSegment 438501421 438566957).card = 231 := by
  simpa using combineTwinPrimeSegments (by decide : 438501421 ≤ 438534189)
    (by decide : 438534189 ≤ 438566957) block2 block3

theorem join_1_0 : (twinPrimeSegment 438435885 438566957).card = 458 := by
  simpa using combineTwinPrimeSegments (by decide : 438435885 ≤ 438501421)
    (by decide : 438501421 ≤ 438566957) join_0_0 join_0_1

theorem total : (twinPrimeSegment 438435885 438566957).card = 458 := join_1_0

end S209C01
end Sude.GeneratedTwinScan
