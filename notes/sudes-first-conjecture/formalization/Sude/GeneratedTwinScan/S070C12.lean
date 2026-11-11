import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S070C12
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 148373549 148406317 = 125 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 148373549 148406317).card = 125 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 148373549 148406317
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 148406317 148439085 = 121 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 148406317 148439085).card = 121 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 148406317 148439085
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 148439085 148471853 = 108 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 148439085 148471853).card = 108 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 148439085 148471853
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 148471853 148504621 = 118 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 148471853 148504621).card = 118 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 148471853 148504621
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 148373549 148439085).card = 246 := by
  simpa using combineTwinPrimeSegments (by decide : 148373549 ≤ 148406317)
    (by decide : 148406317 ≤ 148439085) block0 block1

theorem join_0_1 : (twinPrimeSegment 148439085 148504621).card = 226 := by
  simpa using combineTwinPrimeSegments (by decide : 148439085 ≤ 148471853)
    (by decide : 148471853 ≤ 148504621) block2 block3

theorem join_1_0 : (twinPrimeSegment 148373549 148504621).card = 472 := by
  simpa using combineTwinPrimeSegments (by decide : 148373549 ≤ 148439085)
    (by decide : 148439085 ≤ 148504621) join_0_0 join_0_1

theorem total : (twinPrimeSegment 148373549 148504621).card = 472 := join_1_0

end S070C12
end Sude.GeneratedTwinScan
