import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S199C06
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20448)) 418119725 418152493 = 106 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 418119725 418152493).card = 106 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20448 418119725 418152493
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20449)) 418152493 418185261 = 126 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 418152493 418185261).card = 126 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20449 418152493 418185261
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20450)) 418185261 418218029 = 113 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 418185261 418218029).card = 113 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20450 418185261 418218029
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20451)) 418218029 418250797 = 102 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 418218029 418250797).card = 102 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20451 418218029 418250797
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 418119725 418185261).card = 232 := by
  simpa using combineTwinPrimeSegments (by decide : 418119725 ≤ 418152493)
    (by decide : 418152493 ≤ 418185261) block0 block1

theorem join_0_1 : (twinPrimeSegment 418185261 418250797).card = 215 := by
  simpa using combineTwinPrimeSegments (by decide : 418185261 ≤ 418218029)
    (by decide : 418218029 ≤ 418250797) block2 block3

theorem join_1_0 : (twinPrimeSegment 418119725 418250797).card = 447 := by
  simpa using combineTwinPrimeSegments (by decide : 418119725 ≤ 418185261)
    (by decide : 418185261 ≤ 418250797) join_0_0 join_0_1

theorem total : (twinPrimeSegment 418119725 418250797).card = 447 := join_1_0

end S199C06
end Sude.GeneratedTwinScan
