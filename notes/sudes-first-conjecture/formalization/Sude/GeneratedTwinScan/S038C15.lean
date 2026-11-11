import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S038C15
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 81657901 81690669 = 140 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 81657901 81690669).card = 140 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 81657901 81690669
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 81690669 81723437 = 119 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 81690669 81723437).card = 119 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 81690669 81723437
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 81723437 81756205 = 138 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 81723437 81756205).card = 138 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 81723437 81756205
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 81756205 81788973 = 128 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 81756205 81788973).card = 128 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 81756205 81788973
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 81657901 81723437).card = 259 := by
  simpa using combineTwinPrimeSegments (by decide : 81657901 ≤ 81690669)
    (by decide : 81690669 ≤ 81723437) block0 block1

theorem join_0_1 : (twinPrimeSegment 81723437 81788973).card = 266 := by
  simpa using combineTwinPrimeSegments (by decide : 81723437 ≤ 81756205)
    (by decide : 81756205 ≤ 81788973) block2 block3

theorem join_1_0 : (twinPrimeSegment 81657901 81788973).card = 525 := by
  simpa using combineTwinPrimeSegments (by decide : 81657901 ≤ 81723437)
    (by decide : 81723437 ≤ 81788973) join_0_0 join_0_1

theorem total : (twinPrimeSegment 81657901 81788973).card = 525 := join_1_0

end S038C15
end Sude.GeneratedTwinScan
