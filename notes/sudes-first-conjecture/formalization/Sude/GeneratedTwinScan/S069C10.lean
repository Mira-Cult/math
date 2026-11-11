import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S069C10
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 146014253 146047021 = 130 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 146014253 146047021).card = 130 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 146014253 146047021
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 146047021 146079789 = 124 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 146047021 146079789).card = 124 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 146047021 146079789
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 146079789 146112557 = 116 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 146079789 146112557).card = 116 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 146079789 146112557
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 146112557 146145325 = 120 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 146112557 146145325).card = 120 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 146112557 146145325
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 146014253 146079789).card = 254 := by
  simpa using combineTwinPrimeSegments (by decide : 146014253 ≤ 146047021)
    (by decide : 146047021 ≤ 146079789) block0 block1

theorem join_0_1 : (twinPrimeSegment 146079789 146145325).card = 236 := by
  simpa using combineTwinPrimeSegments (by decide : 146079789 ≤ 146112557)
    (by decide : 146112557 ≤ 146145325) block2 block3

theorem join_1_0 : (twinPrimeSegment 146014253 146145325).card = 490 := by
  simpa using combineTwinPrimeSegments (by decide : 146014253 ≤ 146079789)
    (by decide : 146079789 ≤ 146145325) join_0_0 join_0_1

theorem total : (twinPrimeSegment 146014253 146145325).card = 490 := join_1_0

end S069C10
end Sude.GeneratedTwinScan
