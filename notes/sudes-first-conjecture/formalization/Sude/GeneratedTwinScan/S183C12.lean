import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S183C12
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19631)) 385351725 385384493 = 106 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 385351725 385384493).card = 106 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19631 385351725 385384493
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19632)) 385384493 385417261 = 97 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 385384493 385417261).card = 97 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19632 385384493 385417261
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19632)) 385417261 385450029 = 111 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 385417261 385450029).card = 111 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19632 385417261 385450029
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19633)) 385450029 385482797 = 107 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 385450029 385482797).card = 107 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19633 385450029 385482797
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 385351725 385417261).card = 203 := by
  simpa using combineTwinPrimeSegments (by decide : 385351725 ≤ 385384493)
    (by decide : 385384493 ≤ 385417261) block0 block1

theorem join_0_1 : (twinPrimeSegment 385417261 385482797).card = 218 := by
  simpa using combineTwinPrimeSegments (by decide : 385417261 ≤ 385450029)
    (by decide : 385450029 ≤ 385482797) block2 block3

theorem join_1_0 : (twinPrimeSegment 385351725 385482797).card = 421 := by
  simpa using combineTwinPrimeSegments (by decide : 385351725 ≤ 385417261)
    (by decide : 385417261 ≤ 385482797) join_0_0 join_0_1

theorem total : (twinPrimeSegment 385351725 385482797).card = 421 := join_1_0

end S183C12
end Sude.GeneratedTwinScan
