import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S055C02
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 115605549 115638317 = 137 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 115605549 115638317).card = 137 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 115605549 115638317
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 115638317 115671085 = 119 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 115638317 115671085).card = 119 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 115638317 115671085
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 115671085 115703853 = 127 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 115671085 115703853).card = 127 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 115671085 115703853
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 115703853 115736621 = 128 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 115703853 115736621).card = 128 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 115703853 115736621
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 115605549 115671085).card = 256 := by
  simpa using combineTwinPrimeSegments (by decide : 115605549 ≤ 115638317)
    (by decide : 115638317 ≤ 115671085) block0 block1

theorem join_0_1 : (twinPrimeSegment 115671085 115736621).card = 255 := by
  simpa using combineTwinPrimeSegments (by decide : 115671085 ≤ 115703853)
    (by decide : 115703853 ≤ 115736621) block2 block3

theorem join_1_0 : (twinPrimeSegment 115605549 115736621).card = 511 := by
  simpa using combineTwinPrimeSegments (by decide : 115605549 ≤ 115671085)
    (by decide : 115671085 ≤ 115736621) join_0_0 join_0_1

theorem total : (twinPrimeSegment 115605549 115736621).card = 511 := join_1_0

end S055C02
end Sude.GeneratedTwinScan
