import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S234C08
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22176)) 491782189 491814957 = 104 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 491782189 491814957).card = 104 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22176 491782189 491814957
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22177)) 491814957 491847725 = 129 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 491814957 491847725).card = 129 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22177 491814957 491847725
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22178)) 491847725 491880493 = 103 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 491847725 491880493).card = 103 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22178 491847725 491880493
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22179)) 491880493 491913261 = 96 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 491880493 491913261).card = 96 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22179 491880493 491913261
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 491782189 491847725).card = 233 := by
  simpa using combineTwinPrimeSegments (by decide : 491782189 ≤ 491814957)
    (by decide : 491814957 ≤ 491847725) block0 block1

theorem join_0_1 : (twinPrimeSegment 491847725 491913261).card = 199 := by
  simpa using combineTwinPrimeSegments (by decide : 491847725 ≤ 491880493)
    (by decide : 491880493 ≤ 491913261) block2 block3

theorem join_1_0 : (twinPrimeSegment 491782189 491913261).card = 432 := by
  simpa using combineTwinPrimeSegments (by decide : 491782189 ≤ 491847725)
    (by decide : 491847725 ≤ 491913261) join_0_0 join_0_1

theorem total : (twinPrimeSegment 491782189 491913261).card = 432 := join_1_0

end S234C08
end Sude.GeneratedTwinScan
