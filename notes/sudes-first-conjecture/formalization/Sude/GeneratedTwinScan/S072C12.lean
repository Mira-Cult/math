import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S072C12
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 152567853 152600621 = 113 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 152567853 152600621).card = 113 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 152567853 152600621
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 152600621 152633389 = 130 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 152600621 152633389).card = 130 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 152600621 152633389
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 152633389 152666157 = 119 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 152633389 152666157).card = 119 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 152633389 152666157
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 152666157 152698925 = 120 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 152666157 152698925).card = 120 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 152666157 152698925
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 152567853 152633389).card = 243 := by
  simpa using combineTwinPrimeSegments (by decide : 152567853 ≤ 152600621)
    (by decide : 152600621 ≤ 152633389) block0 block1

theorem join_0_1 : (twinPrimeSegment 152633389 152698925).card = 239 := by
  simpa using combineTwinPrimeSegments (by decide : 152633389 ≤ 152666157)
    (by decide : 152666157 ≤ 152698925) block2 block3

theorem join_1_0 : (twinPrimeSegment 152567853 152698925).card = 482 := by
  simpa using combineTwinPrimeSegments (by decide : 152567853 ≤ 152633389)
    (by decide : 152633389 ≤ 152698925) join_0_0 join_0_1

theorem total : (twinPrimeSegment 152567853 152698925).card = 482 := join_1_0

end S072C12
end Sude.GeneratedTwinScan
