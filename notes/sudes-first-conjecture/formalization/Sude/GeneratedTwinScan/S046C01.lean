import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S046C01
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 96600109 96632877 = 124 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 96600109 96632877).card = 124 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 96600109 96632877
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 96632877 96665645 = 120 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 96632877 96665645).card = 120 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 96632877 96665645
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 96665645 96698413 = 133 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 96665645 96698413).card = 133 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 96665645 96698413
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 96698413 96731181 = 103 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 96698413 96731181).card = 103 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 96698413 96731181
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 96600109 96665645).card = 244 := by
  simpa using combineTwinPrimeSegments (by decide : 96600109 ≤ 96632877)
    (by decide : 96632877 ≤ 96665645) block0 block1

theorem join_0_1 : (twinPrimeSegment 96665645 96731181).card = 236 := by
  simpa using combineTwinPrimeSegments (by decide : 96665645 ≤ 96698413)
    (by decide : 96698413 ≤ 96731181) block2 block3

theorem join_1_0 : (twinPrimeSegment 96600109 96731181).card = 480 := by
  simpa using combineTwinPrimeSegments (by decide : 96600109 ≤ 96665645)
    (by decide : 96665645 ≤ 96731181) join_0_0 join_0_1

theorem total : (twinPrimeSegment 96600109 96731181).card = 480 := join_1_0

end S046C01
end Sude.GeneratedTwinScan
