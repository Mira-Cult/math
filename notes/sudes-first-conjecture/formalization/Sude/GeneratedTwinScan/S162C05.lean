import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S162C05
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18450)) 340394029 340426797 = 117 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 340394029 340426797).card = 117 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18450 340394029 340426797
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18451)) 340426797 340459565 = 105 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 340426797 340459565).card = 105 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18451 340426797 340459565
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18452)) 340459565 340492333 = 116 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 340459565 340492333).card = 116 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18452 340459565 340492333
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18453)) 340492333 340525101 = 109 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 340492333 340525101).card = 109 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18453 340492333 340525101
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 340394029 340459565).card = 222 := by
  simpa using combineTwinPrimeSegments (by decide : 340394029 ≤ 340426797)
    (by decide : 340426797 ≤ 340459565) block0 block1

theorem join_0_1 : (twinPrimeSegment 340459565 340525101).card = 225 := by
  simpa using combineTwinPrimeSegments (by decide : 340459565 ≤ 340492333)
    (by decide : 340492333 ≤ 340525101) block2 block3

theorem join_1_0 : (twinPrimeSegment 340394029 340525101).card = 447 := by
  simpa using combineTwinPrimeSegments (by decide : 340394029 ≤ 340459565)
    (by decide : 340459565 ≤ 340525101) join_0_0 join_0_1

theorem total : (twinPrimeSegment 340394029 340525101).card = 447 := join_1_0

end S162C05
end Sude.GeneratedTwinScan
