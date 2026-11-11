import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S084C03
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13288)) 176554029 176586797 = 111 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 176554029 176586797).card = 111 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13288 176554029 176586797
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13289)) 176586797 176619565 = 135 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 176586797 176619565).card = 135 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13289 176586797 176619565
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13291)) 176619565 176652333 = 117 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 176619565 176652333).card = 117 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13291 176619565 176652333
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13292)) 176652333 176685101 = 105 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 176652333 176685101).card = 105 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13292 176652333 176685101
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 176554029 176619565).card = 246 := by
  simpa using combineTwinPrimeSegments (by decide : 176554029 ≤ 176586797)
    (by decide : 176586797 ≤ 176619565) block0 block1

theorem join_0_1 : (twinPrimeSegment 176619565 176685101).card = 222 := by
  simpa using combineTwinPrimeSegments (by decide : 176619565 ≤ 176652333)
    (by decide : 176652333 ≤ 176685101) block2 block3

theorem join_1_0 : (twinPrimeSegment 176554029 176685101).card = 468 := by
  simpa using combineTwinPrimeSegments (by decide : 176554029 ≤ 176619565)
    (by decide : 176619565 ≤ 176685101) join_0_0 join_0_1

theorem total : (twinPrimeSegment 176554029 176685101).card = 468 := join_1_0

end S084C03
end Sude.GeneratedTwinScan
