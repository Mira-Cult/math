import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S042C09
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 89260077 89292845 = 138 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 89260077 89292845).card = 138 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 89260077 89292845
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 89292845 89325613 = 130 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 89292845 89325613).card = 130 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 89292845 89325613
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 89325613 89358381 = 149 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 89325613 89358381).card = 149 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 89325613 89358381
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 89358381 89391149 = 103 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 89358381 89391149).card = 103 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 89358381 89391149
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 89260077 89325613).card = 268 := by
  simpa using combineTwinPrimeSegments (by decide : 89260077 ≤ 89292845)
    (by decide : 89292845 ≤ 89325613) block0 block1

theorem join_0_1 : (twinPrimeSegment 89325613 89391149).card = 252 := by
  simpa using combineTwinPrimeSegments (by decide : 89325613 ≤ 89358381)
    (by decide : 89358381 ≤ 89391149) block2 block3

theorem join_1_0 : (twinPrimeSegment 89260077 89391149).card = 520 := by
  simpa using combineTwinPrimeSegments (by decide : 89260077 ≤ 89325613)
    (by decide : 89325613 ≤ 89391149) join_0_0 join_0_1

theorem total : (twinPrimeSegment 89260077 89391149).card = 520 := join_1_0

end S042C09
end Sude.GeneratedTwinScan
