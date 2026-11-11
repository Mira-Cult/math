import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S069C00
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 144703533 144736301 = 122 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 144703533 144736301).card = 122 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 144703533 144736301
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 144736301 144769069 = 128 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 144736301 144769069).card = 128 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 144736301 144769069
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 144769069 144801837 = 117 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 144769069 144801837).card = 117 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 144769069 144801837
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 144801837 144834605 = 119 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 144801837 144834605).card = 119 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 144801837 144834605
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 144703533 144769069).card = 250 := by
  simpa using combineTwinPrimeSegments (by decide : 144703533 ≤ 144736301)
    (by decide : 144736301 ≤ 144769069) block0 block1

theorem join_0_1 : (twinPrimeSegment 144769069 144834605).card = 236 := by
  simpa using combineTwinPrimeSegments (by decide : 144769069 ≤ 144801837)
    (by decide : 144801837 ≤ 144834605) block2 block3

theorem join_1_0 : (twinPrimeSegment 144703533 144834605).card = 486 := by
  simpa using combineTwinPrimeSegments (by decide : 144703533 ≤ 144769069)
    (by decide : 144769069 ≤ 144834605) join_0_0 join_0_1

theorem total : (twinPrimeSegment 144703533 144834605).card = 486 := join_1_0

end S069C00
end Sude.GeneratedTwinScan
