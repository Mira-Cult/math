import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S207C07
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20858)) 435028013 435060781 = 110 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 435028013 435060781).card = 110 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20858 435028013 435060781
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20858)) 435060781 435093549 = 103 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 435060781 435093549).card = 103 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20858 435060781 435093549
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20859)) 435093549 435126317 = 99 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 435093549 435126317).card = 99 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20859 435093549 435126317
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20860)) 435126317 435159085 = 106 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 435126317 435159085).card = 106 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20860 435126317 435159085
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 435028013 435093549).card = 213 := by
  simpa using combineTwinPrimeSegments (by decide : 435028013 ≤ 435060781)
    (by decide : 435060781 ≤ 435093549) block0 block1

theorem join_0_1 : (twinPrimeSegment 435093549 435159085).card = 205 := by
  simpa using combineTwinPrimeSegments (by decide : 435093549 ≤ 435126317)
    (by decide : 435126317 ≤ 435159085) block2 block3

theorem join_1_0 : (twinPrimeSegment 435028013 435159085).card = 418 := by
  simpa using combineTwinPrimeSegments (by decide : 435028013 ≤ 435093549)
    (by decide : 435093549 ≤ 435159085) join_0_0 join_0_1

theorem total : (twinPrimeSegment 435028013 435159085).card = 418 := join_1_0

end S207C07
end Sude.GeneratedTwinScan
