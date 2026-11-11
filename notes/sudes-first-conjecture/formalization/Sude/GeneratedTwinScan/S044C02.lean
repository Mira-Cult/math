import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S044C02
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 92536877 92569645 = 130 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 92536877 92569645).card = 130 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 92536877 92569645
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 92569645 92602413 = 129 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 92569645 92602413).card = 129 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 92569645 92602413
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 92602413 92635181 = 139 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 92602413 92635181).card = 139 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 92602413 92635181
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 92635181 92667949 = 132 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 92635181 92667949).card = 132 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 92635181 92667949
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 92536877 92602413).card = 259 := by
  simpa using combineTwinPrimeSegments (by decide : 92536877 ≤ 92569645)
    (by decide : 92569645 ≤ 92602413) block0 block1

theorem join_0_1 : (twinPrimeSegment 92602413 92667949).card = 271 := by
  simpa using combineTwinPrimeSegments (by decide : 92602413 ≤ 92635181)
    (by decide : 92635181 ≤ 92667949) block2 block3

theorem join_1_0 : (twinPrimeSegment 92536877 92667949).card = 530 := by
  simpa using combineTwinPrimeSegments (by decide : 92536877 ≤ 92602413)
    (by decide : 92602413 ≤ 92667949) join_0_0 join_0_1

theorem total : (twinPrimeSegment 92536877 92667949).card = 530 := join_1_0

end S044C02
end Sude.GeneratedTwinScan
