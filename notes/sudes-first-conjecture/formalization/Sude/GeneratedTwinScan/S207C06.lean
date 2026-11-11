import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S207C06
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20854)) 434896941 434929709 = 110 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 434896941 434929709).card = 110 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20854 434896941 434929709
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20855)) 434929709 434962477 = 104 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 434929709 434962477).card = 104 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20855 434929709 434962477
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20856)) 434962477 434995245 = 112 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 434962477 434995245).card = 112 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20856 434962477 434995245
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20857)) 434995245 435028013 = 104 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 434995245 435028013).card = 104 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20857 434995245 435028013
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 434896941 434962477).card = 214 := by
  simpa using combineTwinPrimeSegments (by decide : 434896941 ≤ 434929709)
    (by decide : 434929709 ≤ 434962477) block0 block1

theorem join_0_1 : (twinPrimeSegment 434962477 435028013).card = 216 := by
  simpa using combineTwinPrimeSegments (by decide : 434962477 ≤ 434995245)
    (by decide : 434995245 ≤ 435028013) block2 block3

theorem join_1_0 : (twinPrimeSegment 434896941 435028013).card = 430 := by
  simpa using combineTwinPrimeSegments (by decide : 434896941 ≤ 434962477)
    (by decide : 434962477 ≤ 435028013) join_0_0 join_0_1

theorem total : (twinPrimeSegment 434896941 435028013).card = 430 := join_1_0

end S207C06
end Sude.GeneratedTwinScan
