import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S058C03
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 122028077 122060845 = 134 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 122028077 122060845).card = 134 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 122028077 122060845
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 122060845 122093613 = 132 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 122060845 122093613).card = 132 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 122060845 122093613
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 122093613 122126381 = 137 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 122093613 122126381).card = 137 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 122093613 122126381
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 122126381 122159149 = 108 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 122126381 122159149).card = 108 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 122126381 122159149
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 122028077 122093613).card = 266 := by
  simpa using combineTwinPrimeSegments (by decide : 122028077 ≤ 122060845)
    (by decide : 122060845 ≤ 122093613) block0 block1

theorem join_0_1 : (twinPrimeSegment 122093613 122159149).card = 245 := by
  simpa using combineTwinPrimeSegments (by decide : 122093613 ≤ 122126381)
    (by decide : 122126381 ≤ 122159149) block2 block3

theorem join_1_0 : (twinPrimeSegment 122028077 122159149).card = 511 := by
  simpa using combineTwinPrimeSegments (by decide : 122028077 ≤ 122093613)
    (by decide : 122093613 ≤ 122159149) join_0_0 join_0_1

theorem total : (twinPrimeSegment 122028077 122159149).card = 511 := join_1_0

end S058C03
end Sude.GeneratedTwinScan
