import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S071C15
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 150863917 150896685 = 118 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 150863917 150896685).card = 118 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 150863917 150896685
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 150896685 150929453 = 109 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 150896685 150929453).card = 109 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 150896685 150929453
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 150929453 150962221 = 126 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 150929453 150962221).card = 126 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 150929453 150962221
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 150962221 150994989 = 103 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 150962221 150994989).card = 103 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 150962221 150994989
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 150863917 150929453).card = 227 := by
  simpa using combineTwinPrimeSegments (by decide : 150863917 ≤ 150896685)
    (by decide : 150896685 ≤ 150929453) block0 block1

theorem join_0_1 : (twinPrimeSegment 150929453 150994989).card = 229 := by
  simpa using combineTwinPrimeSegments (by decide : 150929453 ≤ 150962221)
    (by decide : 150962221 ≤ 150994989) block2 block3

theorem join_1_0 : (twinPrimeSegment 150863917 150994989).card = 456 := by
  simpa using combineTwinPrimeSegments (by decide : 150863917 ≤ 150929453)
    (by decide : 150929453 ≤ 150994989) join_0_0 join_0_1

theorem total : (twinPrimeSegment 150863917 150994989).card = 456 := join_1_0

end S071C15
end Sude.GeneratedTwinScan
