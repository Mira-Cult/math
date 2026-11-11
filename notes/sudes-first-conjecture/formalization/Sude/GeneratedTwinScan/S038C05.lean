import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S038C05
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 80347181 80379949 = 119 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 80347181 80379949).card = 119 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 80347181 80379949
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 80379949 80412717 = 145 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 80379949 80412717).card = 145 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 80379949 80412717
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 80412717 80445485 = 126 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 80412717 80445485).card = 126 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 80412717 80445485
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 80445485 80478253 = 129 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 80445485 80478253).card = 129 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 80445485 80478253
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 80347181 80412717).card = 264 := by
  simpa using combineTwinPrimeSegments (by decide : 80347181 ≤ 80379949)
    (by decide : 80379949 ≤ 80412717) block0 block1

theorem join_0_1 : (twinPrimeSegment 80412717 80478253).card = 255 := by
  simpa using combineTwinPrimeSegments (by decide : 80412717 ≤ 80445485)
    (by decide : 80445485 ≤ 80478253) block2 block3

theorem join_1_0 : (twinPrimeSegment 80347181 80478253).card = 519 := by
  simpa using combineTwinPrimeSegments (by decide : 80347181 ≤ 80412717)
    (by decide : 80412717 ≤ 80478253) join_0_0 join_0_1

theorem total : (twinPrimeSegment 80347181 80478253).card = 519 := join_1_0

end S038C05
end Sude.GeneratedTwinScan
