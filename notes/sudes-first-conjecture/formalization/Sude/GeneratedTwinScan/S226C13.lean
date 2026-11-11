import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S226C13
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21810)) 475660333 475693101 = 117 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 475660333 475693101).card = 117 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21810 475660333 475693101
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21811)) 475693101 475725869 = 116 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 475693101 475725869).card = 116 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21811 475693101 475725869
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21811)) 475725869 475758637 = 119 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 475725869 475758637).card = 119 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21811 475725869 475758637
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21812)) 475758637 475791405 = 112 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 475758637 475791405).card = 112 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21812 475758637 475791405
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 475660333 475725869).card = 233 := by
  simpa using combineTwinPrimeSegments (by decide : 475660333 ≤ 475693101)
    (by decide : 475693101 ≤ 475725869) block0 block1

theorem join_0_1 : (twinPrimeSegment 475725869 475791405).card = 231 := by
  simpa using combineTwinPrimeSegments (by decide : 475725869 ≤ 475758637)
    (by decide : 475758637 ≤ 475791405) block2 block3

theorem join_1_0 : (twinPrimeSegment 475660333 475791405).card = 464 := by
  simpa using combineTwinPrimeSegments (by decide : 475660333 ≤ 475725869)
    (by decide : 475725869 ≤ 475791405) join_0_0 join_0_1

theorem total : (twinPrimeSegment 475660333 475791405).card = 464 := join_1_0

end S226C13
end Sude.GeneratedTwinScan
