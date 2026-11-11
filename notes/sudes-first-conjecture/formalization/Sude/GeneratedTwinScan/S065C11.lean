import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S065C11
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 137756717 137789485 = 125 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 137756717 137789485).card = 125 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 137756717 137789485
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 137789485 137822253 = 120 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 137789485 137822253).card = 120 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 137789485 137822253
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 137822253 137855021 = 122 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 137822253 137855021).card = 122 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 137822253 137855021
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 137855021 137887789 = 107 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 137855021 137887789).card = 107 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 137855021 137887789
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 137756717 137822253).card = 245 := by
  simpa using combineTwinPrimeSegments (by decide : 137756717 ≤ 137789485)
    (by decide : 137789485 ≤ 137822253) block0 block1

theorem join_0_1 : (twinPrimeSegment 137822253 137887789).card = 229 := by
  simpa using combineTwinPrimeSegments (by decide : 137822253 ≤ 137855021)
    (by decide : 137855021 ≤ 137887789) block2 block3

theorem join_1_0 : (twinPrimeSegment 137756717 137887789).card = 474 := by
  simpa using combineTwinPrimeSegments (by decide : 137756717 ≤ 137822253)
    (by decide : 137822253 ≤ 137887789) join_0_0 join_0_1

theorem total : (twinPrimeSegment 137756717 137887789).card = 474 := join_1_0

end S065C11
end Sude.GeneratedTwinScan
