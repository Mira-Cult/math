import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S132C10
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16678)) 278134829 278167597 = 106 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 278134829 278167597).card = 106 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16678 278134829 278167597
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16679)) 278167597 278200365 = 116 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 278167597 278200365).card = 116 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16679 278167597 278200365
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16680)) 278200365 278233133 = 116 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 278200365 278233133).card = 116 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16680 278200365 278233133
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16681)) 278233133 278265901 = 124 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 278233133 278265901).card = 124 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16681 278233133 278265901
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 278134829 278200365).card = 222 := by
  simpa using combineTwinPrimeSegments (by decide : 278134829 ≤ 278167597)
    (by decide : 278167597 ≤ 278200365) block0 block1

theorem join_0_1 : (twinPrimeSegment 278200365 278265901).card = 240 := by
  simpa using combineTwinPrimeSegments (by decide : 278200365 ≤ 278233133)
    (by decide : 278233133 ≤ 278265901) block2 block3

theorem join_1_0 : (twinPrimeSegment 278134829 278265901).card = 462 := by
  simpa using combineTwinPrimeSegments (by decide : 278134829 ≤ 278200365)
    (by decide : 278200365 ≤ 278265901) join_0_0 join_0_1

theorem total : (twinPrimeSegment 278134829 278265901).card = 462 := join_1_0

end S132C10
end Sude.GeneratedTwinScan
