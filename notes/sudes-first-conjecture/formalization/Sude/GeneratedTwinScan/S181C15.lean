import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S181C15
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19534)) 381550637 381583405 = 127 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 381550637 381583405).card = 127 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19534 381550637 381583405
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19534)) 381583405 381616173 = 102 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 381583405 381616173).card = 102 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19534 381583405 381616173
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19535)) 381616173 381648941 = 98 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 381616173 381648941).card = 98 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19535 381616173 381648941
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19536)) 381648941 381681709 = 120 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 381648941 381681709).card = 120 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19536 381648941 381681709
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 381550637 381616173).card = 229 := by
  simpa using combineTwinPrimeSegments (by decide : 381550637 ≤ 381583405)
    (by decide : 381583405 ≤ 381616173) block0 block1

theorem join_0_1 : (twinPrimeSegment 381616173 381681709).card = 218 := by
  simpa using combineTwinPrimeSegments (by decide : 381616173 ≤ 381648941)
    (by decide : 381648941 ≤ 381681709) block2 block3

theorem join_1_0 : (twinPrimeSegment 381550637 381681709).card = 447 := by
  simpa using combineTwinPrimeSegments (by decide : 381550637 ≤ 381616173)
    (by decide : 381616173 ≤ 381681709) join_0_0 join_0_1

theorem total : (twinPrimeSegment 381550637 381681709).card = 447 := join_1_0

end S181C15
end Sude.GeneratedTwinScan
