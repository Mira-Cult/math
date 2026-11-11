import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S039C03
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 82182189 82214957 = 122 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 82182189 82214957).card = 122 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 82182189 82214957
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 82214957 82247725 = 129 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 82214957 82247725).card = 129 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 82214957 82247725
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 82247725 82280493 = 137 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 82247725 82280493).card = 137 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 82247725 82280493
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 82280493 82313261 = 128 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 82280493 82313261).card = 128 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 82280493 82313261
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 82182189 82247725).card = 251 := by
  simpa using combineTwinPrimeSegments (by decide : 82182189 ≤ 82214957)
    (by decide : 82214957 ≤ 82247725) block0 block1

theorem join_0_1 : (twinPrimeSegment 82247725 82313261).card = 265 := by
  simpa using combineTwinPrimeSegments (by decide : 82247725 ≤ 82280493)
    (by decide : 82280493 ≤ 82313261) block2 block3

theorem join_1_0 : (twinPrimeSegment 82182189 82313261).card = 516 := by
  simpa using combineTwinPrimeSegments (by decide : 82182189 ≤ 82247725)
    (by decide : 82247725 ≤ 82313261) join_0_0 join_0_1

theorem total : (twinPrimeSegment 82182189 82313261).card = 516 := join_1_0

end S039C03
end Sude.GeneratedTwinScan
