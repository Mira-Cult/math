import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S068C08
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 143654957 143687725 = 124 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 143654957 143687725).card = 124 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 143654957 143687725
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 143687725 143720493 = 112 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 143687725 143720493).card = 112 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 143687725 143720493
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 143720493 143753261 = 122 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 143720493 143753261).card = 122 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 143720493 143753261
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 143753261 143786029 = 134 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 143753261 143786029).card = 134 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 143753261 143786029
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 143654957 143720493).card = 236 := by
  simpa using combineTwinPrimeSegments (by decide : 143654957 ≤ 143687725)
    (by decide : 143687725 ≤ 143720493) block0 block1

theorem join_0_1 : (twinPrimeSegment 143720493 143786029).card = 256 := by
  simpa using combineTwinPrimeSegments (by decide : 143720493 ≤ 143753261)
    (by decide : 143753261 ≤ 143786029) block2 block3

theorem join_1_0 : (twinPrimeSegment 143654957 143786029).card = 492 := by
  simpa using combineTwinPrimeSegments (by decide : 143654957 ≤ 143720493)
    (by decide : 143720493 ≤ 143786029) join_0_0 join_0_1

theorem total : (twinPrimeSegment 143654957 143786029).card = 492 := join_1_0

end S068C08
end Sude.GeneratedTwinScan
