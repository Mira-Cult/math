import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S054C05
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 113901613 113934381 = 119 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 113901613 113934381).card = 119 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 113901613 113934381
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 113934381 113967149 = 120 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 113934381 113967149).card = 120 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 113934381 113967149
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 113967149 113999917 = 117 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 113967149 113999917).card = 117 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 113967149 113999917
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 113999917 114032685 = 115 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 113999917 114032685).card = 115 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 113999917 114032685
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 113901613 113967149).card = 239 := by
  simpa using combineTwinPrimeSegments (by decide : 113901613 ≤ 113934381)
    (by decide : 113934381 ≤ 113967149) block0 block1

theorem join_0_1 : (twinPrimeSegment 113967149 114032685).card = 232 := by
  simpa using combineTwinPrimeSegments (by decide : 113967149 ≤ 113999917)
    (by decide : 113999917 ≤ 114032685) block2 block3

theorem join_1_0 : (twinPrimeSegment 113901613 114032685).card = 471 := by
  simpa using combineTwinPrimeSegments (by decide : 113901613 ≤ 113967149)
    (by decide : 113967149 ≤ 114032685) join_0_0 join_0_1

theorem total : (twinPrimeSegment 113901613 114032685).card = 471 := join_1_0

end S054C05
end Sude.GeneratedTwinScan
