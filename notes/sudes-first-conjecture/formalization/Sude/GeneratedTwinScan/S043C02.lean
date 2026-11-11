import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S043C02
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 90439725 90472493 = 141 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 90439725 90472493).card = 141 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 90439725 90472493
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 90472493 90505261 = 133 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 90472493 90505261).card = 133 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 90472493 90505261
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 90505261 90538029 = 146 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 90505261 90538029).card = 146 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 90505261 90538029
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 90538029 90570797 = 130 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 90538029 90570797).card = 130 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 90538029 90570797
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 90439725 90505261).card = 274 := by
  simpa using combineTwinPrimeSegments (by decide : 90439725 ≤ 90472493)
    (by decide : 90472493 ≤ 90505261) block0 block1

theorem join_0_1 : (twinPrimeSegment 90505261 90570797).card = 276 := by
  simpa using combineTwinPrimeSegments (by decide : 90505261 ≤ 90538029)
    (by decide : 90538029 ≤ 90570797) block2 block3

theorem join_1_0 : (twinPrimeSegment 90439725 90570797).card = 550 := by
  simpa using combineTwinPrimeSegments (by decide : 90439725 ≤ 90505261)
    (by decide : 90505261 ≤ 90570797) join_0_0 join_0_1

theorem total : (twinPrimeSegment 90439725 90570797).card = 550 := join_1_0

end S043C02
end Sude.GeneratedTwinScan
