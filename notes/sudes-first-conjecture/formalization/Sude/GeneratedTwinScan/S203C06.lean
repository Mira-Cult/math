import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S203C06
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20652)) 426508333 426541101 = 108 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 426508333 426541101).card = 108 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20652 426508333 426541101
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20653)) 426541101 426573869 = 103 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 426541101 426573869).card = 103 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20653 426541101 426573869
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20654)) 426573869 426606637 = 100 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 426573869 426606637).card = 100 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20654 426573869 426606637
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20655)) 426606637 426639405 = 130 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 426606637 426639405).card = 130 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20655 426606637 426639405
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 426508333 426573869).card = 211 := by
  simpa using combineTwinPrimeSegments (by decide : 426508333 ≤ 426541101)
    (by decide : 426541101 ≤ 426573869) block0 block1

theorem join_0_1 : (twinPrimeSegment 426573869 426639405).card = 230 := by
  simpa using combineTwinPrimeSegments (by decide : 426573869 ≤ 426606637)
    (by decide : 426606637 ≤ 426639405) block2 block3

theorem join_1_0 : (twinPrimeSegment 426508333 426639405).card = 441 := by
  simpa using combineTwinPrimeSegments (by decide : 426508333 ≤ 426573869)
    (by decide : 426573869 ≤ 426639405) join_0_0 join_0_1

theorem total : (twinPrimeSegment 426508333 426639405).card = 441 := join_1_0

end S203C06
end Sude.GeneratedTwinScan
