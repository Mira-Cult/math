import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S064C04
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 134742061 134774829 = 151 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 134742061 134774829).card = 151 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 134742061 134774829
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 134774829 134807597 = 118 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 134774829 134807597).card = 118 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 134774829 134807597
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 134807597 134840365 = 136 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 134807597 134840365).card = 136 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 134807597 134840365
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 134840365 134873133 = 118 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 134840365 134873133).card = 118 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 134840365 134873133
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 134742061 134807597).card = 269 := by
  simpa using combineTwinPrimeSegments (by decide : 134742061 ≤ 134774829)
    (by decide : 134774829 ≤ 134807597) block0 block1

theorem join_0_1 : (twinPrimeSegment 134807597 134873133).card = 254 := by
  simpa using combineTwinPrimeSegments (by decide : 134807597 ≤ 134840365)
    (by decide : 134840365 ≤ 134873133) block2 block3

theorem join_1_0 : (twinPrimeSegment 134742061 134873133).card = 523 := by
  simpa using combineTwinPrimeSegments (by decide : 134742061 ≤ 134807597)
    (by decide : 134807597 ≤ 134873133) join_0_0 join_0_1

theorem total : (twinPrimeSegment 134742061 134873133).card = 523 := join_1_0

end S064C04
end Sude.GeneratedTwinScan
