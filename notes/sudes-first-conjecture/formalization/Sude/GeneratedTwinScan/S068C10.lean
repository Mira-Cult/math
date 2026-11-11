import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S068C10
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 143917101 143949869 = 115 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 143917101 143949869).card = 115 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 143917101 143949869
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 143949869 143982637 = 139 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 143949869 143982637).card = 139 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 143949869 143982637
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 143982637 144015405 = 108 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 143982637 144015405).card = 108 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 143982637 144015405
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 144015405 144048173 = 145 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 144015405 144048173).card = 145 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 144015405 144048173
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 143917101 143982637).card = 254 := by
  simpa using combineTwinPrimeSegments (by decide : 143917101 ≤ 143949869)
    (by decide : 143949869 ≤ 143982637) block0 block1

theorem join_0_1 : (twinPrimeSegment 143982637 144048173).card = 253 := by
  simpa using combineTwinPrimeSegments (by decide : 143982637 ≤ 144015405)
    (by decide : 144015405 ≤ 144048173) block2 block3

theorem join_1_0 : (twinPrimeSegment 143917101 144048173).card = 507 := by
  simpa using combineTwinPrimeSegments (by decide : 143917101 ≤ 143982637)
    (by decide : 143982637 ≤ 144048173) join_0_0 join_0_1

theorem total : (twinPrimeSegment 143917101 144048173).card = 507 := join_1_0

end S068C10
end Sude.GeneratedTwinScan
