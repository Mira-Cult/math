import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S036C05
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 76152877 76185645 = 132 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 76152877 76185645).card = 132 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 76152877 76185645
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 76185645 76218413 = 131 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 76185645 76218413).card = 131 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 76185645 76218413
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 76218413 76251181 = 124 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 76218413 76251181).card = 124 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 76218413 76251181
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 76251181 76283949 = 120 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 76251181 76283949).card = 120 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 76251181 76283949
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 76152877 76218413).card = 263 := by
  simpa using combineTwinPrimeSegments (by decide : 76152877 ≤ 76185645)
    (by decide : 76185645 ≤ 76218413) block0 block1

theorem join_0_1 : (twinPrimeSegment 76218413 76283949).card = 244 := by
  simpa using combineTwinPrimeSegments (by decide : 76218413 ≤ 76251181)
    (by decide : 76251181 ≤ 76283949) block2 block3

theorem join_1_0 : (twinPrimeSegment 76152877 76283949).card = 507 := by
  simpa using combineTwinPrimeSegments (by decide : 76152877 ≤ 76218413)
    (by decide : 76218413 ≤ 76283949) join_0_0 join_0_1

theorem total : (twinPrimeSegment 76152877 76283949).card = 507 := join_1_0

end S036C05
end Sude.GeneratedTwinScan
