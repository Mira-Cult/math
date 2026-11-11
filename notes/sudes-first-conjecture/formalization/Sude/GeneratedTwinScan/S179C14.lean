import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S179C14
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19423)) 377225261 377258029 = 131 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 377225261 377258029).card = 131 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19423 377225261 377258029
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19423)) 377258029 377290797 = 113 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 377258029 377290797).card = 113 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19423 377258029 377290797
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19424)) 377290797 377323565 = 109 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 377290797 377323565).card = 109 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19424 377290797 377323565
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19425)) 377323565 377356333 = 116 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 377323565 377356333).card = 116 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19425 377323565 377356333
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 377225261 377290797).card = 244 := by
  simpa using combineTwinPrimeSegments (by decide : 377225261 ≤ 377258029)
    (by decide : 377258029 ≤ 377290797) block0 block1

theorem join_0_1 : (twinPrimeSegment 377290797 377356333).card = 225 := by
  simpa using combineTwinPrimeSegments (by decide : 377290797 ≤ 377323565)
    (by decide : 377323565 ≤ 377356333) block2 block3

theorem join_1_0 : (twinPrimeSegment 377225261 377356333).card = 469 := by
  simpa using combineTwinPrimeSegments (by decide : 377225261 ≤ 377290797)
    (by decide : 377290797 ≤ 377356333) join_0_0 join_0_1

theorem total : (twinPrimeSegment 377225261 377356333).card = 469 := join_1_0

end S179C14
end Sude.GeneratedTwinScan
