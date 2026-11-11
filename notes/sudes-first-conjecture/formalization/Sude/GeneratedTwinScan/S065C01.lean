import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S065C01
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 136445997 136478765 = 122 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 136445997 136478765).card = 122 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 136445997 136478765
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 136478765 136511533 = 131 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 136478765 136511533).card = 131 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 136478765 136511533
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 136511533 136544301 = 130 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 136511533 136544301).card = 130 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 136511533 136544301
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 136544301 136577069 = 121 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 136544301 136577069).card = 121 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 136544301 136577069
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 136445997 136511533).card = 253 := by
  simpa using combineTwinPrimeSegments (by decide : 136445997 ≤ 136478765)
    (by decide : 136478765 ≤ 136511533) block0 block1

theorem join_0_1 : (twinPrimeSegment 136511533 136577069).card = 251 := by
  simpa using combineTwinPrimeSegments (by decide : 136511533 ≤ 136544301)
    (by decide : 136544301 ≤ 136577069) block2 block3

theorem join_1_0 : (twinPrimeSegment 136445997 136577069).card = 504 := by
  simpa using combineTwinPrimeSegments (by decide : 136445997 ≤ 136511533)
    (by decide : 136511533 ≤ 136577069) join_0_0 join_0_1

theorem total : (twinPrimeSegment 136445997 136577069).card = 504 := join_1_0

end S065C01
end Sude.GeneratedTwinScan
