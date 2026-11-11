import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S178C03
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19331)) 373686317 373719085 = 137 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 373686317 373719085).card = 137 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19331 373686317 373719085
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19332)) 373719085 373751853 = 108 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 373719085 373751853).card = 108 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19332 373719085 373751853
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19333)) 373751853 373784621 = 98 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 373751853 373784621).card = 98 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19333 373751853 373784621
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19334)) 373784621 373817389 = 101 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 373784621 373817389).card = 101 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19334 373784621 373817389
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 373686317 373751853).card = 245 := by
  simpa using combineTwinPrimeSegments (by decide : 373686317 ≤ 373719085)
    (by decide : 373719085 ≤ 373751853) block0 block1

theorem join_0_1 : (twinPrimeSegment 373751853 373817389).card = 199 := by
  simpa using combineTwinPrimeSegments (by decide : 373751853 ≤ 373784621)
    (by decide : 373784621 ≤ 373817389) block2 block3

theorem join_1_0 : (twinPrimeSegment 373686317 373817389).card = 444 := by
  simpa using combineTwinPrimeSegments (by decide : 373686317 ≤ 373751853)
    (by decide : 373751853 ≤ 373817389) join_0_0 join_0_1

theorem total : (twinPrimeSegment 373686317 373817389).card = 444 := join_1_0

end S178C03
end Sude.GeneratedTwinScan
