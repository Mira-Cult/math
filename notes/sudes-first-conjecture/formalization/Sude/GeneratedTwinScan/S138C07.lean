import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S138C07
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17039)) 290324525 290357293 = 117 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 290324525 290357293).card = 117 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17039 290324525 290357293
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17040)) 290357293 290390061 = 119 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 290357293 290390061).card = 119 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17040 290357293 290390061
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17041)) 290390061 290422829 = 120 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 290390061 290422829).card = 120 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17041 290390061 290422829
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17042)) 290422829 290455597 = 100 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 290422829 290455597).card = 100 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17042 290422829 290455597
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 290324525 290390061).card = 236 := by
  simpa using combineTwinPrimeSegments (by decide : 290324525 ≤ 290357293)
    (by decide : 290357293 ≤ 290390061) block0 block1

theorem join_0_1 : (twinPrimeSegment 290390061 290455597).card = 220 := by
  simpa using combineTwinPrimeSegments (by decide : 290390061 ≤ 290422829)
    (by decide : 290422829 ≤ 290455597) block2 block3

theorem join_1_0 : (twinPrimeSegment 290324525 290455597).card = 456 := by
  simpa using combineTwinPrimeSegments (by decide : 290324525 ≤ 290390061)
    (by decide : 290390061 ≤ 290455597) join_0_0 join_0_1

theorem total : (twinPrimeSegment 290324525 290455597).card = 456 := join_1_0

end S138C07
end Sude.GeneratedTwinScan
