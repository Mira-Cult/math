import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S061C14
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 129761325 129794093 = 109 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 129761325 129794093).card = 109 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 129761325 129794093
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 129794093 129826861 = 131 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 129794093 129826861).card = 131 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 129794093 129826861
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 129826861 129859629 = 114 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 129826861 129859629).card = 114 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 129826861 129859629
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 129859629 129892397 = 124 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 129859629 129892397).card = 124 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 129859629 129892397
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 129761325 129826861).card = 240 := by
  simpa using combineTwinPrimeSegments (by decide : 129761325 ≤ 129794093)
    (by decide : 129794093 ≤ 129826861) block0 block1

theorem join_0_1 : (twinPrimeSegment 129826861 129892397).card = 238 := by
  simpa using combineTwinPrimeSegments (by decide : 129826861 ≤ 129859629)
    (by decide : 129859629 ≤ 129892397) block2 block3

theorem join_1_0 : (twinPrimeSegment 129761325 129892397).card = 478 := by
  simpa using combineTwinPrimeSegments (by decide : 129761325 ≤ 129826861)
    (by decide : 129826861 ≤ 129892397) join_0_0 join_0_1

theorem total : (twinPrimeSegment 129761325 129892397).card = 478 := join_1_0

end S061C14
end Sude.GeneratedTwinScan
