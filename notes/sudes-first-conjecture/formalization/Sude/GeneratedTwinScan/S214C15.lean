import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S214C15
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21231)) 450756653 450789421 = 103 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 450756653 450789421).card = 103 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21231 450756653 450789421
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21232)) 450789421 450822189 = 109 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 450789421 450822189).card = 109 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21232 450789421 450822189
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21233)) 450822189 450854957 = 103 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 450822189 450854957).card = 103 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21233 450822189 450854957
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21234)) 450854957 450887725 = 116 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 450854957 450887725).card = 116 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21234 450854957 450887725
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 450756653 450822189).card = 212 := by
  simpa using combineTwinPrimeSegments (by decide : 450756653 ≤ 450789421)
    (by decide : 450789421 ≤ 450822189) block0 block1

theorem join_0_1 : (twinPrimeSegment 450822189 450887725).card = 219 := by
  simpa using combineTwinPrimeSegments (by decide : 450822189 ≤ 450854957)
    (by decide : 450854957 ≤ 450887725) block2 block3

theorem join_1_0 : (twinPrimeSegment 450756653 450887725).card = 431 := by
  simpa using combineTwinPrimeSegments (by decide : 450756653 ≤ 450822189)
    (by decide : 450822189 ≤ 450887725) join_0_0 join_0_1

theorem total : (twinPrimeSegment 450756653 450887725).card = 431 := join_1_0

end S214C15
end Sude.GeneratedTwinScan
