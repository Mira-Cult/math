import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S046C13
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 98172973 98205741 = 126 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 98172973 98205741).card = 126 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 98172973 98205741
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 98205741 98238509 = 143 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 98205741 98238509).card = 143 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 98205741 98238509
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 98238509 98271277 = 124 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 98238509 98271277).card = 124 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 98238509 98271277
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 98271277 98304045 = 128 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 98271277 98304045).card = 128 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 98271277 98304045
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 98172973 98238509).card = 269 := by
  simpa using combineTwinPrimeSegments (by decide : 98172973 ≤ 98205741)
    (by decide : 98205741 ≤ 98238509) block0 block1

theorem join_0_1 : (twinPrimeSegment 98238509 98304045).card = 252 := by
  simpa using combineTwinPrimeSegments (by decide : 98238509 ≤ 98271277)
    (by decide : 98271277 ≤ 98304045) block2 block3

theorem join_1_0 : (twinPrimeSegment 98172973 98304045).card = 521 := by
  simpa using combineTwinPrimeSegments (by decide : 98172973 ≤ 98238509)
    (by decide : 98238509 ≤ 98304045) join_0_0 join_0_1

theorem total : (twinPrimeSegment 98172973 98304045).card = 521 := join_1_0

end S046C13
end Sude.GeneratedTwinScan
