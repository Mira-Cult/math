import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S164C09
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18578)) 345112621 345145389 = 115 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 345112621 345145389).card = 115 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18578 345112621 345145389
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18578)) 345145389 345178157 = 102 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 345145389 345178157).card = 102 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18578 345145389 345178157
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18579)) 345178157 345210925 = 105 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 345178157 345210925).card = 105 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18579 345178157 345210925
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18580)) 345210925 345243693 = 122 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 345210925 345243693).card = 122 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18580 345210925 345243693
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 345112621 345178157).card = 217 := by
  simpa using combineTwinPrimeSegments (by decide : 345112621 ≤ 345145389)
    (by decide : 345145389 ≤ 345178157) block0 block1

theorem join_0_1 : (twinPrimeSegment 345178157 345243693).card = 227 := by
  simpa using combineTwinPrimeSegments (by decide : 345178157 ≤ 345210925)
    (by decide : 345210925 ≤ 345243693) block2 block3

theorem join_1_0 : (twinPrimeSegment 345112621 345243693).card = 444 := by
  simpa using combineTwinPrimeSegments (by decide : 345112621 ≤ 345178157)
    (by decide : 345178157 ≤ 345243693) join_0_0 join_0_1

theorem total : (twinPrimeSegment 345112621 345243693).card = 444 := join_1_0

end S164C09
end Sude.GeneratedTwinScan
