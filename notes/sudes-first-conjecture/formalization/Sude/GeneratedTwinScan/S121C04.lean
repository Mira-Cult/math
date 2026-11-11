import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S121C04
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15947)) 254279725 254312493 = 120 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 254279725 254312493).card = 120 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15947 254279725 254312493
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15948)) 254312493 254345261 = 122 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 254312493 254345261).card = 122 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15948 254312493 254345261
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15949)) 254345261 254378029 = 109 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 254345261 254378029).card = 109 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15949 254345261 254378029
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15950)) 254378029 254410797 = 126 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 254378029 254410797).card = 126 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15950 254378029 254410797
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 254279725 254345261).card = 242 := by
  simpa using combineTwinPrimeSegments (by decide : 254279725 ≤ 254312493)
    (by decide : 254312493 ≤ 254345261) block0 block1

theorem join_0_1 : (twinPrimeSegment 254345261 254410797).card = 235 := by
  simpa using combineTwinPrimeSegments (by decide : 254345261 ≤ 254378029)
    (by decide : 254378029 ≤ 254410797) block2 block3

theorem join_1_0 : (twinPrimeSegment 254279725 254410797).card = 477 := by
  simpa using combineTwinPrimeSegments (by decide : 254279725 ≤ 254345261)
    (by decide : 254345261 ≤ 254410797) join_0_0 join_0_1

theorem total : (twinPrimeSegment 254279725 254410797).card = 477 := join_1_0

end S121C04
end Sude.GeneratedTwinScan
