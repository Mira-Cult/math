import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S054C08
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 114294829 114327597 = 133 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 114294829 114327597).card = 133 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 114294829 114327597
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 114327597 114360365 = 134 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 114327597 114360365).card = 134 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 114327597 114360365
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 114360365 114393133 = 122 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 114360365 114393133).card = 122 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 114360365 114393133
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 114393133 114425901 = 137 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 114393133 114425901).card = 137 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 114393133 114425901
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 114294829 114360365).card = 267 := by
  simpa using combineTwinPrimeSegments (by decide : 114294829 ≤ 114327597)
    (by decide : 114327597 ≤ 114360365) block0 block1

theorem join_0_1 : (twinPrimeSegment 114360365 114425901).card = 259 := by
  simpa using combineTwinPrimeSegments (by decide : 114360365 ≤ 114393133)
    (by decide : 114393133 ≤ 114425901) block2 block3

theorem join_1_0 : (twinPrimeSegment 114294829 114425901).card = 526 := by
  simpa using combineTwinPrimeSegments (by decide : 114294829 ≤ 114360365)
    (by decide : 114360365 ≤ 114425901) join_0_0 join_0_1

theorem total : (twinPrimeSegment 114294829 114425901).card = 526 := join_1_0

end S054C08
end Sude.GeneratedTwinScan
