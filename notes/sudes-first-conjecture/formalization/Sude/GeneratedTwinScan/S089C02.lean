import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S089C02
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13672)) 186908717 186941485 = 124 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 186908717 186941485).card = 124 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13672 186908717 186941485
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13673)) 186941485 186974253 = 119 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 186941485 186974253).card = 119 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13673 186941485 186974253
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13675)) 186974253 187007021 = 120 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 186974253 187007021).card = 120 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13675 186974253 187007021
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13676)) 187007021 187039789 = 133 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 187007021 187039789).card = 133 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13676 187007021 187039789
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 186908717 186974253).card = 243 := by
  simpa using combineTwinPrimeSegments (by decide : 186908717 ≤ 186941485)
    (by decide : 186941485 ≤ 186974253) block0 block1

theorem join_0_1 : (twinPrimeSegment 186974253 187039789).card = 253 := by
  simpa using combineTwinPrimeSegments (by decide : 186974253 ≤ 187007021)
    (by decide : 187007021 ≤ 187039789) block2 block3

theorem join_1_0 : (twinPrimeSegment 186908717 187039789).card = 496 := by
  simpa using combineTwinPrimeSegments (by decide : 186908717 ≤ 186974253)
    (by decide : 186974253 ≤ 187039789) join_0_0 join_0_1

theorem total : (twinPrimeSegment 186908717 187039789).card = 496 := join_1_0

end S089C02
end Sude.GeneratedTwinScan
