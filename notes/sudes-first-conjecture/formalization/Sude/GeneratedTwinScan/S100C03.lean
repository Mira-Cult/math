import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S100C03
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14496)) 210108461 210141229 = 109 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 210108461 210141229).card = 109 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14496 210108461 210141229
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14497)) 210141229 210173997 = 111 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 210141229 210173997).card = 111 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14497 210141229 210173997
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14498)) 210173997 210206765 = 128 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 210173997 210206765).card = 128 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14498 210173997 210206765
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14499)) 210206765 210239533 = 112 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 210206765 210239533).card = 112 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14499 210206765 210239533
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 210108461 210173997).card = 220 := by
  simpa using combineTwinPrimeSegments (by decide : 210108461 ≤ 210141229)
    (by decide : 210141229 ≤ 210173997) block0 block1

theorem join_0_1 : (twinPrimeSegment 210173997 210239533).card = 240 := by
  simpa using combineTwinPrimeSegments (by decide : 210173997 ≤ 210206765)
    (by decide : 210206765 ≤ 210239533) block2 block3

theorem join_1_0 : (twinPrimeSegment 210108461 210239533).card = 460 := by
  simpa using combineTwinPrimeSegments (by decide : 210108461 ≤ 210173997)
    (by decide : 210173997 ≤ 210239533) join_0_0 join_0_1

theorem total : (twinPrimeSegment 210108461 210239533).card = 460 := join_1_0

end S100C03
end Sude.GeneratedTwinScan
