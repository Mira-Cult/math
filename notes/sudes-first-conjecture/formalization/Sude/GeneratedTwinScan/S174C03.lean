import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S174C03
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19113)) 365297709 365330477 = 114 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 365297709 365330477).card = 114 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19113 365297709 365330477
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19114)) 365330477 365363245 = 117 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 365330477 365363245).card = 117 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19114 365330477 365363245
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19115)) 365363245 365396013 = 103 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 365363245 365396013).card = 103 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19115 365363245 365396013
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19116)) 365396013 365428781 = 115 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 365396013 365428781).card = 115 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19116 365396013 365428781
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 365297709 365363245).card = 231 := by
  simpa using combineTwinPrimeSegments (by decide : 365297709 ≤ 365330477)
    (by decide : 365330477 ≤ 365363245) block0 block1

theorem join_0_1 : (twinPrimeSegment 365363245 365428781).card = 218 := by
  simpa using combineTwinPrimeSegments (by decide : 365363245 ≤ 365396013)
    (by decide : 365396013 ≤ 365428781) block2 block3

theorem join_1_0 : (twinPrimeSegment 365297709 365428781).card = 449 := by
  simpa using combineTwinPrimeSegments (by decide : 365297709 ≤ 365363245)
    (by decide : 365363245 ≤ 365428781) join_0_0 join_0_1

theorem total : (twinPrimeSegment 365297709 365428781).card = 449 := join_1_0

end S174C03
end Sude.GeneratedTwinScan
