import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S042C03
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 88473645 88506413 = 101 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 88473645 88506413).card = 101 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 88473645 88506413
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 88506413 88539181 = 131 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 88506413 88539181).card = 131 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 88506413 88539181
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 88539181 88571949 = 128 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 88539181 88571949).card = 128 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 88539181 88571949
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 88571949 88604717 = 113 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 88571949 88604717).card = 113 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 88571949 88604717
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 88473645 88539181).card = 232 := by
  simpa using combineTwinPrimeSegments (by decide : 88473645 ≤ 88506413)
    (by decide : 88506413 ≤ 88539181) block0 block1

theorem join_0_1 : (twinPrimeSegment 88539181 88604717).card = 241 := by
  simpa using combineTwinPrimeSegments (by decide : 88539181 ≤ 88571949)
    (by decide : 88571949 ≤ 88604717) block2 block3

theorem join_1_0 : (twinPrimeSegment 88473645 88604717).card = 473 := by
  simpa using combineTwinPrimeSegments (by decide : 88473645 ≤ 88539181)
    (by decide : 88539181 ≤ 88604717) join_0_0 join_0_1

theorem total : (twinPrimeSegment 88473645 88604717).card = 473 := join_1_0

end S042C03
end Sude.GeneratedTwinScan
