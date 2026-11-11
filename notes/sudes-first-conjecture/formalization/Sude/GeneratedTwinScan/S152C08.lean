import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S152C08
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17884)) 319815725 319848493 = 126 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 319815725 319848493).card = 126 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17884 319815725 319848493
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17885)) 319848493 319881261 = 105 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 319848493 319881261).card = 105 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17885 319848493 319881261
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17886)) 319881261 319914029 = 113 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 319881261 319914029).card = 113 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17886 319881261 319914029
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17887)) 319914029 319946797 = 114 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 319914029 319946797).card = 114 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17887 319914029 319946797
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 319815725 319881261).card = 231 := by
  simpa using combineTwinPrimeSegments (by decide : 319815725 ≤ 319848493)
    (by decide : 319848493 ≤ 319881261) block0 block1

theorem join_0_1 : (twinPrimeSegment 319881261 319946797).card = 227 := by
  simpa using combineTwinPrimeSegments (by decide : 319881261 ≤ 319914029)
    (by decide : 319914029 ≤ 319946797) block2 block3

theorem join_1_0 : (twinPrimeSegment 319815725 319946797).card = 458 := by
  simpa using combineTwinPrimeSegments (by decide : 319815725 ≤ 319881261)
    (by decide : 319881261 ≤ 319946797) join_0_0 join_0_1

theorem total : (twinPrimeSegment 319815725 319946797).card = 458 := join_1_0

end S152C08
end Sude.GeneratedTwinScan
