import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S075C13
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 12610)) 158990381 159023149 = 127 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 158990381 159023149).card = 127 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 12610 158990381 159023149
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 12611)) 159023149 159055917 = 125 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 159023149 159055917).card = 125 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 12611 159023149 159055917
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 12613)) 159055917 159088685 = 134 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 159055917 159088685).card = 134 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 12613 159055917 159088685
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 12614)) 159088685 159121453 = 114 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 159088685 159121453).card = 114 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 12614 159088685 159121453
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 158990381 159055917).card = 252 := by
  simpa using combineTwinPrimeSegments (by decide : 158990381 ≤ 159023149)
    (by decide : 159023149 ≤ 159055917) block0 block1

theorem join_0_1 : (twinPrimeSegment 159055917 159121453).card = 248 := by
  simpa using combineTwinPrimeSegments (by decide : 159055917 ≤ 159088685)
    (by decide : 159088685 ≤ 159121453) block2 block3

theorem join_1_0 : (twinPrimeSegment 158990381 159121453).card = 500 := by
  simpa using combineTwinPrimeSegments (by decide : 158990381 ≤ 159055917)
    (by decide : 159055917 ≤ 159121453) join_0_0 join_0_1

theorem total : (twinPrimeSegment 158990381 159121453).card = 500 := join_1_0

end S075C13
end Sude.GeneratedTwinScan
