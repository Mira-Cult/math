import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S195C08
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20249)) 409993261 410026029 = 106 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 409993261 410026029).card = 106 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20249 409993261 410026029
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20249)) 410026029 410058797 = 120 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 410026029 410058797).card = 120 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20249 410026029 410058797
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20250)) 410058797 410091565 = 109 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 410058797 410091565).card = 109 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20250 410058797 410091565
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20251)) 410091565 410124333 = 98 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 410091565 410124333).card = 98 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20251 410091565 410124333
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 409993261 410058797).card = 226 := by
  simpa using combineTwinPrimeSegments (by decide : 409993261 ≤ 410026029)
    (by decide : 410026029 ≤ 410058797) block0 block1

theorem join_0_1 : (twinPrimeSegment 410058797 410124333).card = 207 := by
  simpa using combineTwinPrimeSegments (by decide : 410058797 ≤ 410091565)
    (by decide : 410091565 ≤ 410124333) block2 block3

theorem join_1_0 : (twinPrimeSegment 409993261 410124333).card = 433 := by
  simpa using combineTwinPrimeSegments (by decide : 409993261 ≤ 410058797)
    (by decide : 410058797 ≤ 410124333) join_0_0 join_0_1

theorem total : (twinPrimeSegment 409993261 410124333).card = 433 := join_1_0

end S195C08
end Sude.GeneratedTwinScan
