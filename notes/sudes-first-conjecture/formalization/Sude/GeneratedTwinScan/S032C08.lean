import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S032C08
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 68157485 68190253 = 116 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 68157485 68190253).card = 116 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 68157485 68190253
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 68190253 68223021 = 140 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 68190253 68223021).card = 140 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 68190253 68223021
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 68223021 68255789 = 130 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 68223021 68255789).card = 130 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 68223021 68255789
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 68255789 68288557 = 139 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 68255789 68288557).card = 139 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 68255789 68288557
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 68157485 68223021).card = 256 := by
  simpa using combineTwinPrimeSegments (by decide : 68157485 ≤ 68190253)
    (by decide : 68190253 ≤ 68223021) block0 block1

theorem join_0_1 : (twinPrimeSegment 68223021 68288557).card = 269 := by
  simpa using combineTwinPrimeSegments (by decide : 68223021 ≤ 68255789)
    (by decide : 68255789 ≤ 68288557) block2 block3

theorem join_1_0 : (twinPrimeSegment 68157485 68288557).card = 525 := by
  simpa using combineTwinPrimeSegments (by decide : 68157485 ≤ 68223021)
    (by decide : 68223021 ≤ 68288557) join_0_0 join_0_1

theorem total : (twinPrimeSegment 68157485 68288557).card = 525 := join_1_0

end S032C08
end Sude.GeneratedTwinScan
