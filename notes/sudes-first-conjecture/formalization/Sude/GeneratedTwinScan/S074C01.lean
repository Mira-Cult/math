import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S074C01
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 12464)) 155320365 155353133 = 128 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 155320365 155353133).card = 128 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 12464 155320365 155353133
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 12465)) 155353133 155385901 = 121 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 155353133 155385901).card = 121 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 12465 155353133 155385901
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 12466)) 155385901 155418669 = 139 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 155385901 155418669).card = 139 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 12466 155385901 155418669
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 12468)) 155418669 155451437 = 110 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 155418669 155451437).card = 110 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 12468 155418669 155451437
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 155320365 155385901).card = 249 := by
  simpa using combineTwinPrimeSegments (by decide : 155320365 ≤ 155353133)
    (by decide : 155353133 ≤ 155385901) block0 block1

theorem join_0_1 : (twinPrimeSegment 155385901 155451437).card = 249 := by
  simpa using combineTwinPrimeSegments (by decide : 155385901 ≤ 155418669)
    (by decide : 155418669 ≤ 155451437) block2 block3

theorem join_1_0 : (twinPrimeSegment 155320365 155451437).card = 498 := by
  simpa using combineTwinPrimeSegments (by decide : 155320365 ≤ 155385901)
    (by decide : 155385901 ≤ 155451437) join_0_0 join_0_1

theorem total : (twinPrimeSegment 155320365 155451437).card = 498 := join_1_0

end S074C01
end Sude.GeneratedTwinScan
