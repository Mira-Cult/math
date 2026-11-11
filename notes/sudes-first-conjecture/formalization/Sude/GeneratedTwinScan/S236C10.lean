import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S236C10
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22277)) 496238637 496271405 = 105 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 496238637 496271405).card = 105 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22277 496238637 496271405
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22277)) 496271405 496304173 = 118 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 496271405 496304173).card = 118 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22277 496271405 496304173
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22278)) 496304173 496336941 = 106 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 496304173 496336941).card = 106 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22278 496304173 496336941
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22279)) 496336941 496369709 = 114 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 496336941 496369709).card = 114 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22279 496336941 496369709
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 496238637 496304173).card = 223 := by
  simpa using combineTwinPrimeSegments (by decide : 496238637 ≤ 496271405)
    (by decide : 496271405 ≤ 496304173) block0 block1

theorem join_0_1 : (twinPrimeSegment 496304173 496369709).card = 220 := by
  simpa using combineTwinPrimeSegments (by decide : 496304173 ≤ 496336941)
    (by decide : 496336941 ≤ 496369709) block2 block3

theorem join_1_0 : (twinPrimeSegment 496238637 496369709).card = 443 := by
  simpa using combineTwinPrimeSegments (by decide : 496238637 ≤ 496304173)
    (by decide : 496304173 ≤ 496369709) join_0_0 join_0_1

theorem total : (twinPrimeSegment 496238637 496369709).card = 443 := join_1_0

end S236C10
end Sude.GeneratedTwinScan
