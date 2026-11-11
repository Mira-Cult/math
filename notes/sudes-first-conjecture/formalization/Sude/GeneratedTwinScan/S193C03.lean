import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S193C03
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20128)) 405143597 405176365 = 102 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 405143597 405176365).card = 102 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20128 405143597 405176365
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20129)) 405176365 405209133 = 111 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 405176365 405209133).card = 111 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20129 405176365 405209133
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20130)) 405209133 405241901 = 119 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 405209133 405241901).card = 119 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20130 405209133 405241901
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20131)) 405241901 405274669 = 111 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 405241901 405274669).card = 111 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20131 405241901 405274669
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 405143597 405209133).card = 213 := by
  simpa using combineTwinPrimeSegments (by decide : 405143597 ≤ 405176365)
    (by decide : 405176365 ≤ 405209133) block0 block1

theorem join_0_1 : (twinPrimeSegment 405209133 405274669).card = 230 := by
  simpa using combineTwinPrimeSegments (by decide : 405209133 ≤ 405241901)
    (by decide : 405241901 ≤ 405274669) block2 block3

theorem join_1_0 : (twinPrimeSegment 405143597 405274669).card = 443 := by
  simpa using combineTwinPrimeSegments (by decide : 405143597 ≤ 405209133)
    (by decide : 405209133 ≤ 405274669) join_0_0 join_0_1

theorem total : (twinPrimeSegment 405143597 405274669).card = 443 := join_1_0

end S193C03
end Sude.GeneratedTwinScan
