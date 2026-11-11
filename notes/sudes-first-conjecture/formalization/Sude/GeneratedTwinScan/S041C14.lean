import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S041C14
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 87818285 87851053 = 135 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 87818285 87851053).card = 135 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 87818285 87851053
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 87851053 87883821 = 144 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 87851053 87883821).card = 144 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 87851053 87883821
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 87883821 87916589 = 139 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 87883821 87916589).card = 139 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 87883821 87916589
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 87916589 87949357 = 134 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 87916589 87949357).card = 134 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 87916589 87949357
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 87818285 87883821).card = 279 := by
  simpa using combineTwinPrimeSegments (by decide : 87818285 ≤ 87851053)
    (by decide : 87851053 ≤ 87883821) block0 block1

theorem join_0_1 : (twinPrimeSegment 87883821 87949357).card = 273 := by
  simpa using combineTwinPrimeSegments (by decide : 87883821 ≤ 87916589)
    (by decide : 87916589 ≤ 87949357) block2 block3

theorem join_1_0 : (twinPrimeSegment 87818285 87949357).card = 552 := by
  simpa using combineTwinPrimeSegments (by decide : 87818285 ≤ 87883821)
    (by decide : 87883821 ≤ 87949357) join_0_0 join_0_1

theorem total : (twinPrimeSegment 87818285 87949357).card = 552 := join_1_0

end S041C14
end Sude.GeneratedTwinScan
