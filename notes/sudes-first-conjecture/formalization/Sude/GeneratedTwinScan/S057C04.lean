import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S057C04
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 120061997 120094765 = 146 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 120061997 120094765).card = 146 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 120061997 120094765
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 120094765 120127533 = 122 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 120094765 120127533).card = 122 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 120094765 120127533
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 120127533 120160301 = 114 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 120127533 120160301).card = 114 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 120127533 120160301
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 120160301 120193069 = 126 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 120160301 120193069).card = 126 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 120160301 120193069
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 120061997 120127533).card = 268 := by
  simpa using combineTwinPrimeSegments (by decide : 120061997 ≤ 120094765)
    (by decide : 120094765 ≤ 120127533) block0 block1

theorem join_0_1 : (twinPrimeSegment 120127533 120193069).card = 240 := by
  simpa using combineTwinPrimeSegments (by decide : 120127533 ≤ 120160301)
    (by decide : 120160301 ≤ 120193069) block2 block3

theorem join_1_0 : (twinPrimeSegment 120061997 120193069).card = 508 := by
  simpa using combineTwinPrimeSegments (by decide : 120061997 ≤ 120127533)
    (by decide : 120127533 ≤ 120193069) join_0_0 join_0_1

theorem total : (twinPrimeSegment 120061997 120193069).card = 508 := join_1_0

end S057C04
end Sude.GeneratedTwinScan
