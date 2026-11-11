import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S165C15
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18655)) 347996205 348028973 = 117 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 347996205 348028973).card = 117 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18655 347996205 348028973
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18656)) 348028973 348061741 = 114 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 348028973 348061741).card = 114 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18656 348028973 348061741
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18657)) 348061741 348094509 = 106 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 348061741 348094509).card = 106 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18657 348061741 348094509
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18658)) 348094509 348127277 = 101 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 348094509 348127277).card = 101 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18658 348094509 348127277
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 347996205 348061741).card = 231 := by
  simpa using combineTwinPrimeSegments (by decide : 347996205 ≤ 348028973)
    (by decide : 348028973 ≤ 348061741) block0 block1

theorem join_0_1 : (twinPrimeSegment 348061741 348127277).card = 207 := by
  simpa using combineTwinPrimeSegments (by decide : 348061741 ≤ 348094509)
    (by decide : 348094509 ≤ 348127277) block2 block3

theorem join_1_0 : (twinPrimeSegment 347996205 348127277).card = 438 := by
  simpa using combineTwinPrimeSegments (by decide : 347996205 ≤ 348061741)
    (by decide : 348061741 ≤ 348127277) join_0_0 join_0_1

theorem total : (twinPrimeSegment 347996205 348127277).card = 438 := join_1_0

end S165C15
end Sude.GeneratedTwinScan
