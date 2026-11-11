import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S086C06
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13460)) 181141549 181174317 = 113 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 181141549 181174317).card = 113 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13460 181141549 181174317
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13461)) 181174317 181207085 = 131 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 181174317 181207085).card = 131 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13461 181174317 181207085
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13462)) 181207085 181239853 = 115 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 181207085 181239853).card = 115 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13462 181207085 181239853
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13463)) 181239853 181272621 = 123 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 181239853 181272621).card = 123 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13463 181239853 181272621
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 181141549 181207085).card = 244 := by
  simpa using combineTwinPrimeSegments (by decide : 181141549 ≤ 181174317)
    (by decide : 181174317 ≤ 181207085) block0 block1

theorem join_0_1 : (twinPrimeSegment 181207085 181272621).card = 238 := by
  simpa using combineTwinPrimeSegments (by decide : 181207085 ≤ 181239853)
    (by decide : 181239853 ≤ 181272621) block2 block3

theorem join_1_0 : (twinPrimeSegment 181141549 181272621).card = 482 := by
  simpa using combineTwinPrimeSegments (by decide : 181141549 ≤ 181207085)
    (by decide : 181207085 ≤ 181272621) join_0_0 join_0_1

theorem total : (twinPrimeSegment 181141549 181272621).card = 482 := join_1_0

end S086C06
end Sude.GeneratedTwinScan
