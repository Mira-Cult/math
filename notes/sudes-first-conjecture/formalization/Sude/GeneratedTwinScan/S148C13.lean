import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S148C13
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17666)) 312082477 312115245 = 115 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 312082477 312115245).card = 115 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17666 312082477 312115245
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17667)) 312115245 312148013 = 115 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 312115245 312148013).card = 115 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17667 312115245 312148013
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17668)) 312148013 312180781 = 128 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 312148013 312180781).card = 128 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17668 312148013 312180781
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17669)) 312180781 312213549 = 110 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 312180781 312213549).card = 110 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17669 312180781 312213549
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 312082477 312148013).card = 230 := by
  simpa using combineTwinPrimeSegments (by decide : 312082477 ≤ 312115245)
    (by decide : 312115245 ≤ 312148013) block0 block1

theorem join_0_1 : (twinPrimeSegment 312148013 312213549).card = 238 := by
  simpa using combineTwinPrimeSegments (by decide : 312148013 ≤ 312180781)
    (by decide : 312180781 ≤ 312213549) block2 block3

theorem join_1_0 : (twinPrimeSegment 312082477 312213549).card = 468 := by
  simpa using combineTwinPrimeSegments (by decide : 312082477 ≤ 312148013)
    (by decide : 312148013 ≤ 312213549) join_0_0 join_0_1

theorem total : (twinPrimeSegment 312082477 312213549).card = 468 := join_1_0

end S148C13
end Sude.GeneratedTwinScan
