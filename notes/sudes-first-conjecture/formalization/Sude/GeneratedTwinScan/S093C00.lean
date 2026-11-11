import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S093C00
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13966)) 195035181 195067949 = 108 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 195035181 195067949).card = 108 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13966 195035181 195067949
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13967)) 195067949 195100717 = 110 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 195067949 195100717).card = 110 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13967 195067949 195100717
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13969)) 195100717 195133485 = 139 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 195100717 195133485).card = 139 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13969 195100717 195133485
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13970)) 195133485 195166253 = 120 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 195133485 195166253).card = 120 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13970 195133485 195166253
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 195035181 195100717).card = 218 := by
  simpa using combineTwinPrimeSegments (by decide : 195035181 ≤ 195067949)
    (by decide : 195067949 ≤ 195100717) block0 block1

theorem join_0_1 : (twinPrimeSegment 195100717 195166253).card = 259 := by
  simpa using combineTwinPrimeSegments (by decide : 195100717 ≤ 195133485)
    (by decide : 195133485 ≤ 195166253) block2 block3

theorem join_1_0 : (twinPrimeSegment 195035181 195166253).card = 477 := by
  simpa using combineTwinPrimeSegments (by decide : 195035181 ≤ 195100717)
    (by decide : 195100717 ≤ 195166253) join_0_0 join_0_1

theorem total : (twinPrimeSegment 195035181 195166253).card = 477 := join_1_0

end S093C00
end Sude.GeneratedTwinScan
