import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S168C05
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18788)) 352976941 353009709 = 108 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 352976941 353009709).card = 108 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18788 352976941 353009709
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18789)) 353009709 353042477 = 85 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 353009709 353042477).card = 85 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18789 353009709 353042477
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18790)) 353042477 353075245 = 121 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 353042477 353075245).card = 121 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18790 353042477 353075245
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18791)) 353075245 353108013 = 116 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 353075245 353108013).card = 116 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18791 353075245 353108013
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 352976941 353042477).card = 193 := by
  simpa using combineTwinPrimeSegments (by decide : 352976941 ≤ 353009709)
    (by decide : 353009709 ≤ 353042477) block0 block1

theorem join_0_1 : (twinPrimeSegment 353042477 353108013).card = 237 := by
  simpa using combineTwinPrimeSegments (by decide : 353042477 ≤ 353075245)
    (by decide : 353075245 ≤ 353108013) block2 block3

theorem join_1_0 : (twinPrimeSegment 352976941 353108013).card = 430 := by
  simpa using combineTwinPrimeSegments (by decide : 352976941 ≤ 353042477)
    (by decide : 353042477 ≤ 353108013) join_0_0 join_0_1

theorem total : (twinPrimeSegment 352976941 353108013).card = 430 := join_1_0

end S168C05
end Sude.GeneratedTwinScan
