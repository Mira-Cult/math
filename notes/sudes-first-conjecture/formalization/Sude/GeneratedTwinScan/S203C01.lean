import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S203C01
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20636)) 425852973 425885741 = 100 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 425852973 425885741).card = 100 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20636 425852973 425885741
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20637)) 425885741 425918509 = 107 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 425885741 425918509).card = 107 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20637 425885741 425918509
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20638)) 425918509 425951277 = 116 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 425918509 425951277).card = 116 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20638 425918509 425951277
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20639)) 425951277 425984045 = 115 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 425951277 425984045).card = 115 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20639 425951277 425984045
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 425852973 425918509).card = 207 := by
  simpa using combineTwinPrimeSegments (by decide : 425852973 ≤ 425885741)
    (by decide : 425885741 ≤ 425918509) block0 block1

theorem join_0_1 : (twinPrimeSegment 425918509 425984045).card = 231 := by
  simpa using combineTwinPrimeSegments (by decide : 425918509 ≤ 425951277)
    (by decide : 425951277 ≤ 425984045) block2 block3

theorem join_1_0 : (twinPrimeSegment 425852973 425984045).card = 438 := by
  simpa using combineTwinPrimeSegments (by decide : 425852973 ≤ 425918509)
    (by decide : 425918509 ≤ 425984045) join_0_0 join_0_1

theorem total : (twinPrimeSegment 425852973 425984045).card = 438 := join_1_0

end S203C01
end Sude.GeneratedTwinScan
