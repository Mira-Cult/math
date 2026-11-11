import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S187C11
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19840)) 393609261 393642029 = 113 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 393609261 393642029).card = 113 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19840 393609261 393642029
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19841)) 393642029 393674797 = 105 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 393642029 393674797).card = 105 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19841 393642029 393674797
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19842)) 393674797 393707565 = 108 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 393674797 393707565).card = 108 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19842 393674797 393707565
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19842)) 393707565 393740333 = 112 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 393707565 393740333).card = 112 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19842 393707565 393740333
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 393609261 393674797).card = 218 := by
  simpa using combineTwinPrimeSegments (by decide : 393609261 ≤ 393642029)
    (by decide : 393642029 ≤ 393674797) block0 block1

theorem join_0_1 : (twinPrimeSegment 393674797 393740333).card = 220 := by
  simpa using combineTwinPrimeSegments (by decide : 393674797 ≤ 393707565)
    (by decide : 393707565 ≤ 393740333) block2 block3

theorem join_1_0 : (twinPrimeSegment 393609261 393740333).card = 438 := by
  simpa using combineTwinPrimeSegments (by decide : 393609261 ≤ 393674797)
    (by decide : 393674797 ≤ 393740333) join_0_0 join_0_1

theorem total : (twinPrimeSegment 393609261 393740333).card = 438 := join_1_0

end S187C11
end Sude.GeneratedTwinScan
