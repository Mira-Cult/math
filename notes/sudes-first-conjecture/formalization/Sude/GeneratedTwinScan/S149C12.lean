import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S149C12
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17722)) 314048557 314081325 = 124 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 314048557 314081325).card = 124 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17722 314048557 314081325
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17723)) 314081325 314114093 = 108 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 314081325 314114093).card = 108 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17723 314081325 314114093
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17724)) 314114093 314146861 = 115 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 314114093 314146861).card = 115 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17724 314114093 314146861
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17725)) 314146861 314179629 = 106 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 314146861 314179629).card = 106 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17725 314146861 314179629
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 314048557 314114093).card = 232 := by
  simpa using combineTwinPrimeSegments (by decide : 314048557 ≤ 314081325)
    (by decide : 314081325 ≤ 314114093) block0 block1

theorem join_0_1 : (twinPrimeSegment 314114093 314179629).card = 221 := by
  simpa using combineTwinPrimeSegments (by decide : 314114093 ≤ 314146861)
    (by decide : 314146861 ≤ 314179629) block2 block3

theorem join_1_0 : (twinPrimeSegment 314048557 314179629).card = 453 := by
  simpa using combineTwinPrimeSegments (by decide : 314048557 ≤ 314114093)
    (by decide : 314114093 ≤ 314179629) join_0_0 join_0_1

theorem total : (twinPrimeSegment 314048557 314179629).card = 453 := join_1_0

end S149C12
end Sude.GeneratedTwinScan
