import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S039C01
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 81920045 81952813 = 135 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 81920045 81952813).card = 135 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 81920045 81952813
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 81952813 81985581 = 132 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 81952813 81985581).card = 132 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 81952813 81985581
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 81985581 82018349 = 122 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 81985581 82018349).card = 122 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 81985581 82018349
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 82018349 82051117 = 131 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 82018349 82051117).card = 131 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 82018349 82051117
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 81920045 81985581).card = 267 := by
  simpa using combineTwinPrimeSegments (by decide : 81920045 ≤ 81952813)
    (by decide : 81952813 ≤ 81985581) block0 block1

theorem join_0_1 : (twinPrimeSegment 81985581 82051117).card = 253 := by
  simpa using combineTwinPrimeSegments (by decide : 81985581 ≤ 82018349)
    (by decide : 82018349 ≤ 82051117) block2 block3

theorem join_1_0 : (twinPrimeSegment 81920045 82051117).card = 520 := by
  simpa using combineTwinPrimeSegments (by decide : 81920045 ≤ 81985581)
    (by decide : 81985581 ≤ 82051117) join_0_0 join_0_1

theorem total : (twinPrimeSegment 81920045 82051117).card = 520 := join_1_0

end S039C01
end Sude.GeneratedTwinScan
