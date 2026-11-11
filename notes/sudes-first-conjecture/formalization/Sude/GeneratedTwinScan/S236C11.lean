import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S236C11
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22280)) 496369709 496402477 = 103 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 496369709 496402477).card = 103 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22280 496369709 496402477
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22280)) 496402477 496435245 = 111 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 496402477 496435245).card = 111 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22280 496402477 496435245
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22281)) 496435245 496468013 = 107 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 496435245 496468013).card = 107 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22281 496435245 496468013
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22282)) 496468013 496500781 = 101 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 496468013 496500781).card = 101 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22282 496468013 496500781
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 496369709 496435245).card = 214 := by
  simpa using combineTwinPrimeSegments (by decide : 496369709 ≤ 496402477)
    (by decide : 496402477 ≤ 496435245) block0 block1

theorem join_0_1 : (twinPrimeSegment 496435245 496500781).card = 208 := by
  simpa using combineTwinPrimeSegments (by decide : 496435245 ≤ 496468013)
    (by decide : 496468013 ≤ 496500781) block2 block3

theorem join_1_0 : (twinPrimeSegment 496369709 496500781).card = 422 := by
  simpa using combineTwinPrimeSegments (by decide : 496369709 ≤ 496435245)
    (by decide : 496435245 ≤ 496500781) join_0_0 join_0_1

theorem total : (twinPrimeSegment 496369709 496500781).card = 422 := join_1_0

end S236C11
end Sude.GeneratedTwinScan
