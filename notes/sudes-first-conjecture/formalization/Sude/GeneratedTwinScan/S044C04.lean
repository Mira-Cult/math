import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S044C04
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 92799021 92831789 = 145 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 92799021 92831789).card = 145 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 92799021 92831789
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 92831789 92864557 = 112 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 92831789 92864557).card = 112 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 92831789 92864557
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 92864557 92897325 = 131 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 92864557 92897325).card = 131 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 92864557 92897325
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 92897325 92930093 = 140 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 92897325 92930093).card = 140 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 92897325 92930093
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 92799021 92864557).card = 257 := by
  simpa using combineTwinPrimeSegments (by decide : 92799021 ≤ 92831789)
    (by decide : 92831789 ≤ 92864557) block0 block1

theorem join_0_1 : (twinPrimeSegment 92864557 92930093).card = 271 := by
  simpa using combineTwinPrimeSegments (by decide : 92864557 ≤ 92897325)
    (by decide : 92897325 ≤ 92930093) block2 block3

theorem join_1_0 : (twinPrimeSegment 92799021 92930093).card = 528 := by
  simpa using combineTwinPrimeSegments (by decide : 92799021 ≤ 92864557)
    (by decide : 92864557 ≤ 92930093) join_0_0 join_0_1

theorem total : (twinPrimeSegment 92799021 92930093).card = 528 := join_1_0

end S044C04
end Sude.GeneratedTwinScan
