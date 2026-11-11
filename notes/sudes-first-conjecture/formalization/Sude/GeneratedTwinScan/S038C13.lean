import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S038C13
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 81395757 81428525 = 152 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 81395757 81428525).card = 152 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 81395757 81428525
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 81428525 81461293 = 150 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 81428525 81461293).card = 150 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 81428525 81461293
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 81461293 81494061 = 141 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 81461293 81494061).card = 141 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 81461293 81494061
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 81494061 81526829 = 117 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 81494061 81526829).card = 117 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 81494061 81526829
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 81395757 81461293).card = 302 := by
  simpa using combineTwinPrimeSegments (by decide : 81395757 ≤ 81428525)
    (by decide : 81428525 ≤ 81461293) block0 block1

theorem join_0_1 : (twinPrimeSegment 81461293 81526829).card = 258 := by
  simpa using combineTwinPrimeSegments (by decide : 81461293 ≤ 81494061)
    (by decide : 81494061 ≤ 81526829) block2 block3

theorem join_1_0 : (twinPrimeSegment 81395757 81526829).card = 560 := by
  simpa using combineTwinPrimeSegments (by decide : 81395757 ≤ 81461293)
    (by decide : 81461293 ≤ 81526829) join_0_0 join_0_1

theorem total : (twinPrimeSegment 81395757 81526829).card = 560 := join_1_0

end S038C13
end Sude.GeneratedTwinScan
