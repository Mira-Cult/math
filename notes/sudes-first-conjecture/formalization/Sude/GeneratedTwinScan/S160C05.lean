import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S160C05
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18336)) 336199725 336232493 = 104 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 336199725 336232493).card = 104 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18336 336199725 336232493
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18337)) 336232493 336265261 = 112 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 336232493 336265261).card = 112 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18337 336232493 336265261
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18338)) 336265261 336298029 = 114 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 336265261 336298029).card = 114 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18338 336265261 336298029
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18339)) 336298029 336330797 = 111 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 336298029 336330797).card = 111 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18339 336298029 336330797
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 336199725 336265261).card = 216 := by
  simpa using combineTwinPrimeSegments (by decide : 336199725 ≤ 336232493)
    (by decide : 336232493 ≤ 336265261) block0 block1

theorem join_0_1 : (twinPrimeSegment 336265261 336330797).card = 225 := by
  simpa using combineTwinPrimeSegments (by decide : 336265261 ≤ 336298029)
    (by decide : 336298029 ≤ 336330797) block2 block3

theorem join_1_0 : (twinPrimeSegment 336199725 336330797).card = 441 := by
  simpa using combineTwinPrimeSegments (by decide : 336199725 ≤ 336265261)
    (by decide : 336265261 ≤ 336330797) join_0_0 join_0_1

theorem total : (twinPrimeSegment 336199725 336330797).card = 441 := join_1_0

end S160C05
end Sude.GeneratedTwinScan
