import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S061C12
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 129499181 129531949 = 138 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 129499181 129531949).card = 138 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 129499181 129531949
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 129531949 129564717 = 136 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 129531949 129564717).card = 136 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 129531949 129564717
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 129564717 129597485 = 123 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 129564717 129597485).card = 123 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 129564717 129597485
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 129597485 129630253 = 119 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 129597485 129630253).card = 119 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 129597485 129630253
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 129499181 129564717).card = 274 := by
  simpa using combineTwinPrimeSegments (by decide : 129499181 ≤ 129531949)
    (by decide : 129531949 ≤ 129564717) block0 block1

theorem join_0_1 : (twinPrimeSegment 129564717 129630253).card = 242 := by
  simpa using combineTwinPrimeSegments (by decide : 129564717 ≤ 129597485)
    (by decide : 129597485 ≤ 129630253) block2 block3

theorem join_1_0 : (twinPrimeSegment 129499181 129630253).card = 516 := by
  simpa using combineTwinPrimeSegments (by decide : 129499181 ≤ 129564717)
    (by decide : 129564717 ≤ 129630253) join_0_0 join_0_1

theorem total : (twinPrimeSegment 129499181 129630253).card = 516 := join_1_0

end S061C12
end Sude.GeneratedTwinScan
