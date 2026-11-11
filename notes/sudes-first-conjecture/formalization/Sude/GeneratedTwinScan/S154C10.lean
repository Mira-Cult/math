import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S154C10
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18008)) 324272173 324304941 = 103 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 324272173 324304941).card = 103 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18008 324272173 324304941
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18009)) 324304941 324337709 = 104 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 324304941 324337709).card = 104 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18009 324304941 324337709
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18010)) 324337709 324370477 = 130 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 324337709 324370477).card = 130 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18010 324337709 324370477
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18011)) 324370477 324403245 = 107 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 324370477 324403245).card = 107 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18011 324370477 324403245
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 324272173 324337709).card = 207 := by
  simpa using combineTwinPrimeSegments (by decide : 324272173 ≤ 324304941)
    (by decide : 324304941 ≤ 324337709) block0 block1

theorem join_0_1 : (twinPrimeSegment 324337709 324403245).card = 237 := by
  simpa using combineTwinPrimeSegments (by decide : 324337709 ≤ 324370477)
    (by decide : 324370477 ≤ 324403245) block2 block3

theorem join_1_0 : (twinPrimeSegment 324272173 324403245).card = 444 := by
  simpa using combineTwinPrimeSegments (by decide : 324272173 ≤ 324337709)
    (by decide : 324337709 ≤ 324403245) join_0_0 join_0_1

theorem total : (twinPrimeSegment 324272173 324403245).card = 444 := join_1_0

end S154C10
end Sude.GeneratedTwinScan
