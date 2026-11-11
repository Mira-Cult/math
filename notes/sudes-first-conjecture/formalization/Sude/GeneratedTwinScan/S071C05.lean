import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S071C05
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 149553197 149585965 = 112 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 149553197 149585965).card = 112 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 149553197 149585965
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 149585965 149618733 = 124 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 149585965 149618733).card = 124 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 149585965 149618733
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 149618733 149651501 = 112 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 149618733 149651501).card = 112 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 149618733 149651501
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 149651501 149684269 = 124 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 149651501 149684269).card = 124 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 149651501 149684269
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 149553197 149618733).card = 236 := by
  simpa using combineTwinPrimeSegments (by decide : 149553197 ≤ 149585965)
    (by decide : 149585965 ≤ 149618733) block0 block1

theorem join_0_1 : (twinPrimeSegment 149618733 149684269).card = 236 := by
  simpa using combineTwinPrimeSegments (by decide : 149618733 ≤ 149651501)
    (by decide : 149651501 ≤ 149684269) block2 block3

theorem join_1_0 : (twinPrimeSegment 149553197 149684269).card = 472 := by
  simpa using combineTwinPrimeSegments (by decide : 149553197 ≤ 149618733)
    (by decide : 149618733 ≤ 149684269) join_0_0 join_0_1

theorem total : (twinPrimeSegment 149553197 149684269).card = 472 := join_1_0

end S071C05
end Sude.GeneratedTwinScan
