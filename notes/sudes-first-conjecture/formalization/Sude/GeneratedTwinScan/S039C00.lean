import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S039C00
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 81788973 81821741 = 151 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 81788973 81821741).card = 151 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 81788973 81821741
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 81821741 81854509 = 126 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 81821741 81854509).card = 126 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 81821741 81854509
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 81854509 81887277 = 122 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 81854509 81887277).card = 122 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 81854509 81887277
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 81887277 81920045 = 122 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 81887277 81920045).card = 122 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 81887277 81920045
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 81788973 81854509).card = 277 := by
  simpa using combineTwinPrimeSegments (by decide : 81788973 ≤ 81821741)
    (by decide : 81821741 ≤ 81854509) block0 block1

theorem join_0_1 : (twinPrimeSegment 81854509 81920045).card = 244 := by
  simpa using combineTwinPrimeSegments (by decide : 81854509 ≤ 81887277)
    (by decide : 81887277 ≤ 81920045) block2 block3

theorem join_1_0 : (twinPrimeSegment 81788973 81920045).card = 521 := by
  simpa using combineTwinPrimeSegments (by decide : 81788973 ≤ 81854509)
    (by decide : 81854509 ≤ 81920045) join_0_0 join_0_1

theorem total : (twinPrimeSegment 81788973 81920045).card = 521 := join_1_0

end S039C00
end Sude.GeneratedTwinScan
