import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S205C05
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20751)) 430571565 430604333 = 97 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 430571565 430604333).card = 97 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20751 430571565 430604333
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20751)) 430604333 430637101 = 115 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 430604333 430637101).card = 115 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20751 430604333 430637101
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20752)) 430637101 430669869 = 107 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 430637101 430669869).card = 107 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20752 430637101 430669869
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20753)) 430669869 430702637 = 104 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 430669869 430702637).card = 104 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20753 430669869 430702637
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 430571565 430637101).card = 212 := by
  simpa using combineTwinPrimeSegments (by decide : 430571565 ≤ 430604333)
    (by decide : 430604333 ≤ 430637101) block0 block1

theorem join_0_1 : (twinPrimeSegment 430637101 430702637).card = 211 := by
  simpa using combineTwinPrimeSegments (by decide : 430637101 ≤ 430669869)
    (by decide : 430669869 ≤ 430702637) block2 block3

theorem join_1_0 : (twinPrimeSegment 430571565 430702637).card = 423 := by
  simpa using combineTwinPrimeSegments (by decide : 430571565 ≤ 430637101)
    (by decide : 430637101 ≤ 430702637) join_0_0 join_0_1

theorem total : (twinPrimeSegment 430571565 430702637).card = 423 := join_1_0

end S205C05
end Sude.GeneratedTwinScan
