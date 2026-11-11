import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S040C06
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 84672557 84705325 = 111 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 84672557 84705325).card = 111 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 84672557 84705325
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 84705325 84738093 = 129 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 84705325 84738093).card = 129 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 84705325 84738093
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 84738093 84770861 = 132 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 84738093 84770861).card = 132 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 84738093 84770861
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 84770861 84803629 = 130 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 84770861 84803629).card = 130 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 84770861 84803629
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 84672557 84738093).card = 240 := by
  simpa using combineTwinPrimeSegments (by decide : 84672557 ≤ 84705325)
    (by decide : 84705325 ≤ 84738093) block0 block1

theorem join_0_1 : (twinPrimeSegment 84738093 84803629).card = 262 := by
  simpa using combineTwinPrimeSegments (by decide : 84738093 ≤ 84770861)
    (by decide : 84770861 ≤ 84803629) block2 block3

theorem join_1_0 : (twinPrimeSegment 84672557 84803629).card = 502 := by
  simpa using combineTwinPrimeSegments (by decide : 84672557 ≤ 84738093)
    (by decide : 84738093 ≤ 84803629) join_0_0 join_0_1

theorem total : (twinPrimeSegment 84672557 84803629).card = 502 := join_1_0

end S040C06
end Sude.GeneratedTwinScan
