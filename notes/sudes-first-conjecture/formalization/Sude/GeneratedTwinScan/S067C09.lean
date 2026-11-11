import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S067C09
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 141688877 141721645 = 120 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 141688877 141721645).card = 120 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 141688877 141721645
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 141721645 141754413 = 120 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 141721645 141754413).card = 120 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 141721645 141754413
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 141754413 141787181 = 110 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 141754413 141787181).card = 110 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 141754413 141787181
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 141787181 141819949 = 123 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 141787181 141819949).card = 123 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 141787181 141819949
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 141688877 141754413).card = 240 := by
  simpa using combineTwinPrimeSegments (by decide : 141688877 ≤ 141721645)
    (by decide : 141721645 ≤ 141754413) block0 block1

theorem join_0_1 : (twinPrimeSegment 141754413 141819949).card = 233 := by
  simpa using combineTwinPrimeSegments (by decide : 141754413 ≤ 141787181)
    (by decide : 141787181 ≤ 141819949) block2 block3

theorem join_1_0 : (twinPrimeSegment 141688877 141819949).card = 473 := by
  simpa using combineTwinPrimeSegments (by decide : 141688877 ≤ 141754413)
    (by decide : 141754413 ≤ 141819949) join_0_0 join_0_1

theorem total : (twinPrimeSegment 141688877 141819949).card = 473 := join_1_0

end S067C09
end Sude.GeneratedTwinScan
