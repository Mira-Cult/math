import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S180C01
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19433)) 377618477 377651245 = 110 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 377618477 377651245).card = 110 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19433 377618477 377651245
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19434)) 377651245 377684013 = 109 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 377651245 377684013).card = 109 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19434 377651245 377684013
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19434)) 377684013 377716781 = 96 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 377684013 377716781).card = 96 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19434 377684013 377716781
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19435)) 377716781 377749549 = 99 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 377716781 377749549).card = 99 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19435 377716781 377749549
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 377618477 377684013).card = 219 := by
  simpa using combineTwinPrimeSegments (by decide : 377618477 ≤ 377651245)
    (by decide : 377651245 ≤ 377684013) block0 block1

theorem join_0_1 : (twinPrimeSegment 377684013 377749549).card = 195 := by
  simpa using combineTwinPrimeSegments (by decide : 377684013 ≤ 377716781)
    (by decide : 377716781 ≤ 377749549) block2 block3

theorem join_1_0 : (twinPrimeSegment 377618477 377749549).card = 414 := by
  simpa using combineTwinPrimeSegments (by decide : 377618477 ≤ 377684013)
    (by decide : 377684013 ≤ 377749549) join_0_0 join_0_1

theorem total : (twinPrimeSegment 377618477 377749549).card = 414 := join_1_0

end S180C01
end Sude.GeneratedTwinScan
