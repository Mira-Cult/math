import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S088C01
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13590)) 184680493 184713261 = 127 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 184680493 184713261).card = 127 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13590 184680493 184713261
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13592)) 184713261 184746029 = 131 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 184713261 184746029).card = 131 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13592 184713261 184746029
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13593)) 184746029 184778797 = 122 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 184746029 184778797).card = 122 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13593 184746029 184778797
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13594)) 184778797 184811565 = 127 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 184778797 184811565).card = 127 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13594 184778797 184811565
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 184680493 184746029).card = 258 := by
  simpa using combineTwinPrimeSegments (by decide : 184680493 ≤ 184713261)
    (by decide : 184713261 ≤ 184746029) block0 block1

theorem join_0_1 : (twinPrimeSegment 184746029 184811565).card = 249 := by
  simpa using combineTwinPrimeSegments (by decide : 184746029 ≤ 184778797)
    (by decide : 184778797 ≤ 184811565) block2 block3

theorem join_1_0 : (twinPrimeSegment 184680493 184811565).card = 507 := by
  simpa using combineTwinPrimeSegments (by decide : 184680493 ≤ 184746029)
    (by decide : 184746029 ≤ 184811565) join_0_0 join_0_1

theorem total : (twinPrimeSegment 184680493 184811565).card = 507 := join_1_0

end S088C01
end Sude.GeneratedTwinScan
