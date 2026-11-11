import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S244C00
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22621)) 511705133 511737901 = 98 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 511705133 511737901).card = 98 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22621 511705133 511737901
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22622)) 511737901 511770669 = 116 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 511737901 511770669).card = 116 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22622 511737901 511770669
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22623)) 511770669 511803437 = 106 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 511770669 511803437).card = 106 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22623 511770669 511803437
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22623)) 511803437 511836205 = 115 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 511803437 511836205).card = 115 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22623 511803437 511836205
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 511705133 511770669).card = 214 := by
  simpa using combineTwinPrimeSegments (by decide : 511705133 ≤ 511737901)
    (by decide : 511737901 ≤ 511770669) block0 block1

theorem join_0_1 : (twinPrimeSegment 511770669 511836205).card = 221 := by
  simpa using combineTwinPrimeSegments (by decide : 511770669 ≤ 511803437)
    (by decide : 511803437 ≤ 511836205) block2 block3

theorem join_1_0 : (twinPrimeSegment 511705133 511836205).card = 435 := by
  simpa using combineTwinPrimeSegments (by decide : 511705133 ≤ 511770669)
    (by decide : 511770669 ≤ 511836205) join_0_0 join_0_1

theorem total : (twinPrimeSegment 511705133 511836205).card = 435 := join_1_0

end S244C00
end Sude.GeneratedTwinScan
