import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S246C07
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22734)) 516816941 516849709 = 96 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 516816941 516849709).card = 96 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22734 516816941 516849709
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22735)) 516849709 516882477 = 100 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 516849709 516882477).card = 100 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22735 516849709 516882477
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22735)) 516882477 516915245 = 122 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 516882477 516915245).card = 122 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22735 516882477 516915245
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22736)) 516915245 516948013 = 117 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 516915245 516948013).card = 117 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22736 516915245 516948013
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 516816941 516882477).card = 196 := by
  simpa using combineTwinPrimeSegments (by decide : 516816941 ≤ 516849709)
    (by decide : 516849709 ≤ 516882477) block0 block1

theorem join_0_1 : (twinPrimeSegment 516882477 516948013).card = 239 := by
  simpa using combineTwinPrimeSegments (by decide : 516882477 ≤ 516915245)
    (by decide : 516915245 ≤ 516948013) block2 block3

theorem join_1_0 : (twinPrimeSegment 516816941 516948013).card = 435 := by
  simpa using combineTwinPrimeSegments (by decide : 516816941 ≤ 516882477)
    (by decide : 516882477 ≤ 516948013) join_0_0 join_0_1

theorem total : (twinPrimeSegment 516816941 516948013).card = 435 := join_1_0

end S246C07
end Sude.GeneratedTwinScan
