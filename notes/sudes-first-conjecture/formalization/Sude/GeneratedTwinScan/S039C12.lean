import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S039C12
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 83361837 83394605 = 133 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 83361837 83394605).card = 133 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 83361837 83394605
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 83394605 83427373 = 142 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 83394605 83427373).card = 142 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 83394605 83427373
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 83427373 83460141 = 115 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 83427373 83460141).card = 115 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 83427373 83460141
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 83460141 83492909 = 130 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 83460141 83492909).card = 130 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 83460141 83492909
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 83361837 83427373).card = 275 := by
  simpa using combineTwinPrimeSegments (by decide : 83361837 ≤ 83394605)
    (by decide : 83394605 ≤ 83427373) block0 block1

theorem join_0_1 : (twinPrimeSegment 83427373 83492909).card = 245 := by
  simpa using combineTwinPrimeSegments (by decide : 83427373 ≤ 83460141)
    (by decide : 83460141 ≤ 83492909) block2 block3

theorem join_1_0 : (twinPrimeSegment 83361837 83492909).card = 520 := by
  simpa using combineTwinPrimeSegments (by decide : 83361837 ≤ 83427373)
    (by decide : 83427373 ≤ 83492909) join_0_0 join_0_1

theorem total : (twinPrimeSegment 83361837 83492909).card = 520 := join_1_0

end S039C12
end Sude.GeneratedTwinScan
