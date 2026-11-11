import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S051C06
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 107741229 107773997 = 115 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 107741229 107773997).card = 115 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 107741229 107773997
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 107773997 107806765 = 130 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 107773997 107806765).card = 130 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 107773997 107806765
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 107806765 107839533 = 128 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 107806765 107839533).card = 128 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 107806765 107839533
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 107839533 107872301 = 134 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 107839533 107872301).card = 134 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 107839533 107872301
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 107741229 107806765).card = 245 := by
  simpa using combineTwinPrimeSegments (by decide : 107741229 ≤ 107773997)
    (by decide : 107773997 ≤ 107806765) block0 block1

theorem join_0_1 : (twinPrimeSegment 107806765 107872301).card = 262 := by
  simpa using combineTwinPrimeSegments (by decide : 107806765 ≤ 107839533)
    (by decide : 107839533 ≤ 107872301) block2 block3

theorem join_1_0 : (twinPrimeSegment 107741229 107872301).card = 507 := by
  simpa using combineTwinPrimeSegments (by decide : 107741229 ≤ 107806765)
    (by decide : 107806765 ≤ 107872301) join_0_0 join_0_1

theorem total : (twinPrimeSegment 107741229 107872301).card = 507 := join_1_0

end S051C06
end Sude.GeneratedTwinScan
