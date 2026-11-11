import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S238C10
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22371)) 500432941 500465709 = 118 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 500432941 500465709).card = 118 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22371 500432941 500465709
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22371)) 500465709 500498477 = 101 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 500465709 500498477).card = 101 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22371 500465709 500498477
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22372)) 500498477 500531245 = 106 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 500498477 500531245).card = 106 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22372 500498477 500531245
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22373)) 500531245 500564013 = 110 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 500531245 500564013).card = 110 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22373 500531245 500564013
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 500432941 500498477).card = 219 := by
  simpa using combineTwinPrimeSegments (by decide : 500432941 ≤ 500465709)
    (by decide : 500465709 ≤ 500498477) block0 block1

theorem join_0_1 : (twinPrimeSegment 500498477 500564013).card = 216 := by
  simpa using combineTwinPrimeSegments (by decide : 500498477 ≤ 500531245)
    (by decide : 500531245 ≤ 500564013) block2 block3

theorem join_1_0 : (twinPrimeSegment 500432941 500564013).card = 435 := by
  simpa using combineTwinPrimeSegments (by decide : 500432941 ≤ 500498477)
    (by decide : 500498477 ≤ 500564013) join_0_0 join_0_1

theorem total : (twinPrimeSegment 500432941 500564013).card = 435 := join_1_0

end S238C10
end Sude.GeneratedTwinScan
