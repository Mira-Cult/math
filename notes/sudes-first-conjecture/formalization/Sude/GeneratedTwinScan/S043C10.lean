import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S043C10
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 91488301 91521069 = 124 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 91488301 91521069).card = 124 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 91488301 91521069
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 91521069 91553837 = 115 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 91521069 91553837).card = 115 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 91521069 91553837
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 91553837 91586605 = 115 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 91553837 91586605).card = 115 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 91553837 91586605
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 91586605 91619373 = 128 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 91586605 91619373).card = 128 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 91586605 91619373
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 91488301 91553837).card = 239 := by
  simpa using combineTwinPrimeSegments (by decide : 91488301 ≤ 91521069)
    (by decide : 91521069 ≤ 91553837) block0 block1

theorem join_0_1 : (twinPrimeSegment 91553837 91619373).card = 243 := by
  simpa using combineTwinPrimeSegments (by decide : 91553837 ≤ 91586605)
    (by decide : 91586605 ≤ 91619373) block2 block3

theorem join_1_0 : (twinPrimeSegment 91488301 91619373).card = 482 := by
  simpa using combineTwinPrimeSegments (by decide : 91488301 ≤ 91553837)
    (by decide : 91553837 ≤ 91619373) join_0_0 join_0_1

theorem total : (twinPrimeSegment 91488301 91619373).card = 482 := join_1_0

end S043C10
end Sude.GeneratedTwinScan
