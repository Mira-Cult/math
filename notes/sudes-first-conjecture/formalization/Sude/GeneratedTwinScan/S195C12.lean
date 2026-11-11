import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S195C12
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20262)) 410517549 410550317 = 106 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 410517549 410550317).card = 106 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20262 410517549 410550317
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20262)) 410550317 410583085 = 107 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 410550317 410583085).card = 107 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20262 410550317 410583085
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20263)) 410583085 410615853 = 113 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 410583085 410615853).card = 113 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20263 410583085 410615853
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20264)) 410615853 410648621 = 112 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 410615853 410648621).card = 112 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20264 410615853 410648621
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 410517549 410583085).card = 213 := by
  simpa using combineTwinPrimeSegments (by decide : 410517549 ≤ 410550317)
    (by decide : 410550317 ≤ 410583085) block0 block1

theorem join_0_1 : (twinPrimeSegment 410583085 410648621).card = 225 := by
  simpa using combineTwinPrimeSegments (by decide : 410583085 ≤ 410615853)
    (by decide : 410615853 ≤ 410648621) block2 block3

theorem join_1_0 : (twinPrimeSegment 410517549 410648621).card = 438 := by
  simpa using combineTwinPrimeSegments (by decide : 410517549 ≤ 410583085)
    (by decide : 410583085 ≤ 410648621) join_0_0 join_0_1

theorem total : (twinPrimeSegment 410517549 410648621).card = 438 := join_1_0

end S195C12
end Sude.GeneratedTwinScan
