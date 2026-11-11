import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S248C07
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22826)) 521011245 521044013 = 101 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 521011245 521044013).card = 101 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22826 521011245 521044013
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22827)) 521044013 521076781 = 121 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 521044013 521076781).card = 121 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22827 521044013 521076781
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22827)) 521076781 521109549 = 83 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 521076781 521109549).card = 83 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22827 521076781 521109549
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22828)) 521109549 521142317 = 103 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 521109549 521142317).card = 103 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22828 521109549 521142317
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 521011245 521076781).card = 222 := by
  simpa using combineTwinPrimeSegments (by decide : 521011245 ≤ 521044013)
    (by decide : 521044013 ≤ 521076781) block0 block1

theorem join_0_1 : (twinPrimeSegment 521076781 521142317).card = 186 := by
  simpa using combineTwinPrimeSegments (by decide : 521076781 ≤ 521109549)
    (by decide : 521109549 ≤ 521142317) block2 block3

theorem join_1_0 : (twinPrimeSegment 521011245 521142317).card = 408 := by
  simpa using combineTwinPrimeSegments (by decide : 521011245 ≤ 521076781)
    (by decide : 521076781 ≤ 521142317) join_0_0 join_0_1

theorem total : (twinPrimeSegment 521011245 521142317).card = 408 := join_1_0

end S248C07
end Sude.GeneratedTwinScan
