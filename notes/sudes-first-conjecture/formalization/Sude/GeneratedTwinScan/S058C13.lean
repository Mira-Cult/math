import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S058C13
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 123338797 123371565 = 129 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 123338797 123371565).card = 129 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 123338797 123371565
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 123371565 123404333 = 132 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 123371565 123404333).card = 132 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 123371565 123404333
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 123404333 123437101 = 124 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 123404333 123437101).card = 124 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 123404333 123437101
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 123437101 123469869 = 122 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 123437101 123469869).card = 122 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 123437101 123469869
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 123338797 123404333).card = 261 := by
  simpa using combineTwinPrimeSegments (by decide : 123338797 ≤ 123371565)
    (by decide : 123371565 ≤ 123404333) block0 block1

theorem join_0_1 : (twinPrimeSegment 123404333 123469869).card = 246 := by
  simpa using combineTwinPrimeSegments (by decide : 123404333 ≤ 123437101)
    (by decide : 123437101 ≤ 123469869) block2 block3

theorem join_1_0 : (twinPrimeSegment 123338797 123469869).card = 507 := by
  simpa using combineTwinPrimeSegments (by decide : 123338797 ≤ 123404333)
    (by decide : 123404333 ≤ 123469869) join_0_0 join_0_1

theorem total : (twinPrimeSegment 123338797 123469869).card = 507 := join_1_0

end S058C13
end Sude.GeneratedTwinScan
