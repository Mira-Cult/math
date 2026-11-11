import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S200C13
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20522)) 421134381 421167149 = 100 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 421134381 421167149).card = 100 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20522 421134381 421167149
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20523)) 421167149 421199917 = 129 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 421167149 421199917).card = 129 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20523 421167149 421199917
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20523)) 421199917 421232685 = 89 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 421199917 421232685).card = 89 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20523 421199917 421232685
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20524)) 421232685 421265453 = 97 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 421232685 421265453).card = 97 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20524 421232685 421265453
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 421134381 421199917).card = 229 := by
  simpa using combineTwinPrimeSegments (by decide : 421134381 ≤ 421167149)
    (by decide : 421167149 ≤ 421199917) block0 block1

theorem join_0_1 : (twinPrimeSegment 421199917 421265453).card = 186 := by
  simpa using combineTwinPrimeSegments (by decide : 421199917 ≤ 421232685)
    (by decide : 421232685 ≤ 421265453) block2 block3

theorem join_1_0 : (twinPrimeSegment 421134381 421265453).card = 415 := by
  simpa using combineTwinPrimeSegments (by decide : 421134381 ≤ 421199917)
    (by decide : 421199917 ≤ 421265453) join_0_0 join_0_1

theorem total : (twinPrimeSegment 421134381 421265453).card = 415 := join_1_0

end S200C13
end Sude.GeneratedTwinScan
