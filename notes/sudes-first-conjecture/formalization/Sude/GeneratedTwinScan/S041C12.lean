import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S041C12
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 87556141 87588909 = 108 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 87556141 87588909).card = 108 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 87556141 87588909
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 87588909 87621677 = 136 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 87588909 87621677).card = 136 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 87588909 87621677
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 87621677 87654445 = 122 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 87621677 87654445).card = 122 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 87621677 87654445
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 87654445 87687213 = 116 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 87654445 87687213).card = 116 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 87654445 87687213
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 87556141 87621677).card = 244 := by
  simpa using combineTwinPrimeSegments (by decide : 87556141 ≤ 87588909)
    (by decide : 87588909 ≤ 87621677) block0 block1

theorem join_0_1 : (twinPrimeSegment 87621677 87687213).card = 238 := by
  simpa using combineTwinPrimeSegments (by decide : 87621677 ≤ 87654445)
    (by decide : 87654445 ≤ 87687213) block2 block3

theorem join_1_0 : (twinPrimeSegment 87556141 87687213).card = 482 := by
  simpa using combineTwinPrimeSegments (by decide : 87556141 ≤ 87621677)
    (by decide : 87621677 ≤ 87687213) join_0_0 join_0_1

theorem total : (twinPrimeSegment 87556141 87687213).card = 482 := join_1_0

end S041C12
end Sude.GeneratedTwinScan
