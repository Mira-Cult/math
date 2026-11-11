import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S247C11
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22791)) 519438381 519471149 = 105 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 519438381 519471149).card = 105 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22791 519438381 519471149
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22792)) 519471149 519503917 = 118 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 519471149 519503917).card = 118 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22792 519471149 519503917
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22793)) 519503917 519536685 = 109 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 519503917 519536685).card = 109 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22793 519503917 519536685
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22794)) 519536685 519569453 = 98 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 519536685 519569453).card = 98 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22794 519536685 519569453
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 519438381 519503917).card = 223 := by
  simpa using combineTwinPrimeSegments (by decide : 519438381 ≤ 519471149)
    (by decide : 519471149 ≤ 519503917) block0 block1

theorem join_0_1 : (twinPrimeSegment 519503917 519569453).card = 207 := by
  simpa using combineTwinPrimeSegments (by decide : 519503917 ≤ 519536685)
    (by decide : 519536685 ≤ 519569453) block2 block3

theorem join_1_0 : (twinPrimeSegment 519438381 519569453).card = 430 := by
  simpa using combineTwinPrimeSegments (by decide : 519438381 ≤ 519503917)
    (by decide : 519503917 ≤ 519569453) join_0_0 join_0_1

theorem total : (twinPrimeSegment 519438381 519569453).card = 430 := join_1_0

end S247C11
end Sude.GeneratedTwinScan
