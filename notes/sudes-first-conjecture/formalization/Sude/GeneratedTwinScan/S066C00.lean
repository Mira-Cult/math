import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S066C00
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 138412077 138444845 = 119 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 138412077 138444845).card = 119 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 138412077 138444845
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 138444845 138477613 = 125 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 138444845 138477613).card = 125 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 138444845 138477613
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 138477613 138510381 = 115 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 138477613 138510381).card = 115 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 138477613 138510381
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 138510381 138543149 = 133 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 138510381 138543149).card = 133 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 138510381 138543149
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 138412077 138477613).card = 244 := by
  simpa using combineTwinPrimeSegments (by decide : 138412077 ≤ 138444845)
    (by decide : 138444845 ≤ 138477613) block0 block1

theorem join_0_1 : (twinPrimeSegment 138477613 138543149).card = 248 := by
  simpa using combineTwinPrimeSegments (by decide : 138477613 ≤ 138510381)
    (by decide : 138510381 ≤ 138543149) block2 block3

theorem join_1_0 : (twinPrimeSegment 138412077 138543149).card = 492 := by
  simpa using combineTwinPrimeSegments (by decide : 138412077 ≤ 138477613)
    (by decide : 138477613 ≤ 138543149) join_0_0 join_0_1

theorem total : (twinPrimeSegment 138412077 138543149).card = 492 := join_1_0

end S066C00
end Sude.GeneratedTwinScan
