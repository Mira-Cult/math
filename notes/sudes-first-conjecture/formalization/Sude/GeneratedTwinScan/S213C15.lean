import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S213C15
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21182)) 448659501 448692269 = 110 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 448659501 448692269).card = 110 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21182 448659501 448692269
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21183)) 448692269 448725037 = 107 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 448692269 448725037).card = 107 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21183 448692269 448725037
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21183)) 448725037 448757805 = 130 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 448725037 448757805).card = 130 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21183 448725037 448757805
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21184)) 448757805 448790573 = 100 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 448757805 448790573).card = 100 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21184 448757805 448790573
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 448659501 448725037).card = 217 := by
  simpa using combineTwinPrimeSegments (by decide : 448659501 ≤ 448692269)
    (by decide : 448692269 ≤ 448725037) block0 block1

theorem join_0_1 : (twinPrimeSegment 448725037 448790573).card = 230 := by
  simpa using combineTwinPrimeSegments (by decide : 448725037 ≤ 448757805)
    (by decide : 448757805 ≤ 448790573) block2 block3

theorem join_1_0 : (twinPrimeSegment 448659501 448790573).card = 447 := by
  simpa using combineTwinPrimeSegments (by decide : 448659501 ≤ 448725037)
    (by decide : 448725037 ≤ 448790573) join_0_0 join_0_1

theorem total : (twinPrimeSegment 448659501 448790573).card = 447 := join_1_0

end S213C15
end Sude.GeneratedTwinScan
