import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S067C12
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 142082093 142114861 = 102 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 142082093 142114861).card = 102 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 142082093 142114861
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 142114861 142147629 = 128 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 142114861 142147629).card = 128 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 142114861 142147629
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 142147629 142180397 = 128 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 142147629 142180397).card = 128 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 142147629 142180397
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 142180397 142213165 = 130 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 142180397 142213165).card = 130 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 142180397 142213165
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 142082093 142147629).card = 230 := by
  simpa using combineTwinPrimeSegments (by decide : 142082093 ≤ 142114861)
    (by decide : 142114861 ≤ 142147629) block0 block1

theorem join_0_1 : (twinPrimeSegment 142147629 142213165).card = 258 := by
  simpa using combineTwinPrimeSegments (by decide : 142147629 ≤ 142180397)
    (by decide : 142180397 ≤ 142213165) block2 block3

theorem join_1_0 : (twinPrimeSegment 142082093 142213165).card = 488 := by
  simpa using combineTwinPrimeSegments (by decide : 142082093 ≤ 142147629)
    (by decide : 142147629 ≤ 142213165) join_0_0 join_0_1

theorem total : (twinPrimeSegment 142082093 142213165).card = 488 := join_1_0

end S067C12
end Sude.GeneratedTwinScan
