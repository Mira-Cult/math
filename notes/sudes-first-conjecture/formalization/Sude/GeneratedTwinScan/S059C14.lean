import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S059C14
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 125567021 125599789 = 140 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 125567021 125599789).card = 140 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 125567021 125599789
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 125599789 125632557 = 103 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 125599789 125632557).card = 103 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 125599789 125632557
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 125632557 125665325 = 126 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 125632557 125665325).card = 126 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 125632557 125665325
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 125665325 125698093 = 135 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 125665325 125698093).card = 135 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 125665325 125698093
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 125567021 125632557).card = 243 := by
  simpa using combineTwinPrimeSegments (by decide : 125567021 ≤ 125599789)
    (by decide : 125599789 ≤ 125632557) block0 block1

theorem join_0_1 : (twinPrimeSegment 125632557 125698093).card = 261 := by
  simpa using combineTwinPrimeSegments (by decide : 125632557 ≤ 125665325)
    (by decide : 125665325 ≤ 125698093) block2 block3

theorem join_1_0 : (twinPrimeSegment 125567021 125698093).card = 504 := by
  simpa using combineTwinPrimeSegments (by decide : 125567021 ≤ 125632557)
    (by decide : 125632557 ≤ 125698093) join_0_0 join_0_1

theorem total : (twinPrimeSegment 125567021 125698093).card = 504 := join_1_0

end S059C14
end Sude.GeneratedTwinScan
