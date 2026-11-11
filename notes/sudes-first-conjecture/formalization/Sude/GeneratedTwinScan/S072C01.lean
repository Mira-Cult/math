import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S072C01
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 151126061 151158829 = 114 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 151126061 151158829).card = 114 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 151126061 151158829
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 151158829 151191597 = 130 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 151158829 151191597).card = 130 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 151158829 151191597
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 151191597 151224365 = 130 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 151191597 151224365).card = 130 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 151191597 151224365
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 151224365 151257133 = 121 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 151224365 151257133).card = 121 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 151224365 151257133
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 151126061 151191597).card = 244 := by
  simpa using combineTwinPrimeSegments (by decide : 151126061 ≤ 151158829)
    (by decide : 151158829 ≤ 151191597) block0 block1

theorem join_0_1 : (twinPrimeSegment 151191597 151257133).card = 251 := by
  simpa using combineTwinPrimeSegments (by decide : 151191597 ≤ 151224365)
    (by decide : 151224365 ≤ 151257133) block2 block3

theorem join_1_0 : (twinPrimeSegment 151126061 151257133).card = 495 := by
  simpa using combineTwinPrimeSegments (by decide : 151126061 ≤ 151191597)
    (by decide : 151191597 ≤ 151257133) join_0_0 join_0_1

theorem total : (twinPrimeSegment 151126061 151257133).card = 495 := join_1_0

end S072C01
end Sude.GeneratedTwinScan
