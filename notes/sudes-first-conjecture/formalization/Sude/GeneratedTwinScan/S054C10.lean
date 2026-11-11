import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S054C10
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 114556973 114589741 = 118 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 114556973 114589741).card = 118 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 114556973 114589741
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 114589741 114622509 = 126 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 114589741 114622509).card = 126 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 114589741 114622509
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 114622509 114655277 = 133 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 114622509 114655277).card = 133 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 114622509 114655277
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 114655277 114688045 = 118 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 114655277 114688045).card = 118 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 114655277 114688045
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 114556973 114622509).card = 244 := by
  simpa using combineTwinPrimeSegments (by decide : 114556973 ≤ 114589741)
    (by decide : 114589741 ≤ 114622509) block0 block1

theorem join_0_1 : (twinPrimeSegment 114622509 114688045).card = 251 := by
  simpa using combineTwinPrimeSegments (by decide : 114622509 ≤ 114655277)
    (by decide : 114655277 ≤ 114688045) block2 block3

theorem join_1_0 : (twinPrimeSegment 114556973 114688045).card = 495 := by
  simpa using combineTwinPrimeSegments (by decide : 114556973 ≤ 114622509)
    (by decide : 114622509 ≤ 114688045) join_0_0 join_0_1

theorem total : (twinPrimeSegment 114556973 114688045).card = 495 := join_1_0

end S054C10
end Sude.GeneratedTwinScan
