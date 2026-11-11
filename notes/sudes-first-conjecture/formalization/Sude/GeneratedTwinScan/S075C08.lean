import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S075C08
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 12584)) 158335021 158367789 = 124 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 158335021 158367789).card = 124 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 12584 158335021 158367789
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 12585)) 158367789 158400557 = 130 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 158367789 158400557).card = 130 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 12585 158367789 158400557
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 12587)) 158400557 158433325 = 149 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 158400557 158433325).card = 149 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 12587 158400557 158433325
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 12588)) 158433325 158466093 = 119 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 158433325 158466093).card = 119 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 12588 158433325 158466093
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 158335021 158400557).card = 254 := by
  simpa using combineTwinPrimeSegments (by decide : 158335021 ≤ 158367789)
    (by decide : 158367789 ≤ 158400557) block0 block1

theorem join_0_1 : (twinPrimeSegment 158400557 158466093).card = 268 := by
  simpa using combineTwinPrimeSegments (by decide : 158400557 ≤ 158433325)
    (by decide : 158433325 ≤ 158466093) block2 block3

theorem join_1_0 : (twinPrimeSegment 158335021 158466093).card = 522 := by
  simpa using combineTwinPrimeSegments (by decide : 158335021 ≤ 158400557)
    (by decide : 158400557 ≤ 158466093) join_0_0 join_0_1

theorem total : (twinPrimeSegment 158335021 158466093).card = 522 := join_1_0

end S075C08
end Sude.GeneratedTwinScan
