import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S065C10
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 137625645 137658413 = 127 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 137625645 137658413).card = 127 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 137625645 137658413
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 137658413 137691181 = 126 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 137658413 137691181).card = 126 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 137658413 137691181
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 137691181 137723949 = 129 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 137691181 137723949).card = 129 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 137691181 137723949
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 137723949 137756717 = 129 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 137723949 137756717).card = 129 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 137723949 137756717
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 137625645 137691181).card = 253 := by
  simpa using combineTwinPrimeSegments (by decide : 137625645 ≤ 137658413)
    (by decide : 137658413 ≤ 137691181) block0 block1

theorem join_0_1 : (twinPrimeSegment 137691181 137756717).card = 258 := by
  simpa using combineTwinPrimeSegments (by decide : 137691181 ≤ 137723949)
    (by decide : 137723949 ≤ 137756717) block2 block3

theorem join_1_0 : (twinPrimeSegment 137625645 137756717).card = 511 := by
  simpa using combineTwinPrimeSegments (by decide : 137625645 ≤ 137691181)
    (by decide : 137691181 ≤ 137756717) join_0_0 join_0_1

theorem total : (twinPrimeSegment 137625645 137756717).card = 511 := join_1_0

end S065C10
end Sude.GeneratedTwinScan
