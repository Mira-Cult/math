import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S099C06
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14437)) 208404525 208437293 = 123 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 208404525 208437293).card = 123 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14437 208404525 208437293
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14438)) 208437293 208470061 = 129 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 208437293 208470061).card = 129 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14438 208437293 208470061
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14439)) 208470061 208502829 = 133 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 208470061 208502829).card = 133 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14439 208470061 208502829
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14440)) 208502829 208535597 = 98 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 208502829 208535597).card = 98 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14440 208502829 208535597
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 208404525 208470061).card = 252 := by
  simpa using combineTwinPrimeSegments (by decide : 208404525 ≤ 208437293)
    (by decide : 208437293 ≤ 208470061) block0 block1

theorem join_0_1 : (twinPrimeSegment 208470061 208535597).card = 231 := by
  simpa using combineTwinPrimeSegments (by decide : 208470061 ≤ 208502829)
    (by decide : 208502829 ≤ 208535597) block2 block3

theorem join_1_0 : (twinPrimeSegment 208404525 208535597).card = 483 := by
  simpa using combineTwinPrimeSegments (by decide : 208404525 ≤ 208470061)
    (by decide : 208470061 ≤ 208535597) join_0_0 join_0_1

theorem total : (twinPrimeSegment 208404525 208535597).card = 483 := join_1_0

end S099C06
end Sude.GeneratedTwinScan
