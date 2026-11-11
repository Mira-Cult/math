import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S134C07
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16791)) 281935917 281968685 = 102 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 281935917 281968685).card = 102 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16791 281935917 281968685
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16792)) 281968685 282001453 = 128 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 281968685 282001453).card = 128 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16792 281968685 282001453
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16793)) 282001453 282034221 = 117 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 282001453 282034221).card = 117 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16793 282001453 282034221
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16794)) 282034221 282066989 = 106 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 282034221 282066989).card = 106 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16794 282034221 282066989
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 281935917 282001453).card = 230 := by
  simpa using combineTwinPrimeSegments (by decide : 281935917 ≤ 281968685)
    (by decide : 281968685 ≤ 282001453) block0 block1

theorem join_0_1 : (twinPrimeSegment 282001453 282066989).card = 223 := by
  simpa using combineTwinPrimeSegments (by decide : 282001453 ≤ 282034221)
    (by decide : 282034221 ≤ 282066989) block2 block3

theorem join_1_0 : (twinPrimeSegment 281935917 282066989).card = 453 := by
  simpa using combineTwinPrimeSegments (by decide : 281935917 ≤ 282001453)
    (by decide : 282001453 ≤ 282066989) join_0_0 join_0_1

theorem total : (twinPrimeSegment 281935917 282066989).card = 453 := join_1_0

end S134C07
end Sude.GeneratedTwinScan
