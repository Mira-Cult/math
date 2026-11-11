import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S029C07
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 61734957 61767725 = 129 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 61734957 61767725).card = 129 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 61734957 61767725
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 61767725 61800493 = 136 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 61767725 61800493).card = 136 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 61767725 61800493
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 61800493 61833261 = 138 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 61800493 61833261).card = 138 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 61800493 61833261
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 61833261 61866029 = 135 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 61833261 61866029).card = 135 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 61833261 61866029
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 61734957 61800493).card = 265 := by
  simpa using combineTwinPrimeSegments (by decide : 61734957 ≤ 61767725)
    (by decide : 61767725 ≤ 61800493) block0 block1

theorem join_0_1 : (twinPrimeSegment 61800493 61866029).card = 273 := by
  simpa using combineTwinPrimeSegments (by decide : 61800493 ≤ 61833261)
    (by decide : 61833261 ≤ 61866029) block2 block3

theorem join_1_0 : (twinPrimeSegment 61734957 61866029).card = 538 := by
  simpa using combineTwinPrimeSegments (by decide : 61734957 ≤ 61800493)
    (by decide : 61800493 ≤ 61866029) join_0_0 join_0_1

theorem total : (twinPrimeSegment 61734957 61866029).card = 538 := join_1_0

end S029C07
end Sude.GeneratedTwinScan
