import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S189C10
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19942)) 397672493 397705261 = 107 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 397672493 397705261).card = 107 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19942 397672493 397705261
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19943)) 397705261 397738029 = 115 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 397705261 397738029).card = 115 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19943 397705261 397738029
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19944)) 397738029 397770797 = 102 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 397738029 397770797).card = 102 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19944 397738029 397770797
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19945)) 397770797 397803565 = 120 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 397770797 397803565).card = 120 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19945 397770797 397803565
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 397672493 397738029).card = 222 := by
  simpa using combineTwinPrimeSegments (by decide : 397672493 ≤ 397705261)
    (by decide : 397705261 ≤ 397738029) block0 block1

theorem join_0_1 : (twinPrimeSegment 397738029 397803565).card = 222 := by
  simpa using combineTwinPrimeSegments (by decide : 397738029 ≤ 397770797)
    (by decide : 397770797 ≤ 397803565) block2 block3

theorem join_1_0 : (twinPrimeSegment 397672493 397803565).card = 444 := by
  simpa using combineTwinPrimeSegments (by decide : 397672493 ≤ 397738029)
    (by decide : 397738029 ≤ 397803565) join_0_0 join_0_1

theorem total : (twinPrimeSegment 397672493 397803565).card = 444 := join_1_0

end S189C10
end Sude.GeneratedTwinScan
