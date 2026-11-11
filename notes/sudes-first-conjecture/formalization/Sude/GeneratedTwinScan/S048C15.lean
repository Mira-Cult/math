import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S048C15
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 102629421 102662189 = 125 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 102629421 102662189).card = 125 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 102629421 102662189
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 102662189 102694957 = 112 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 102662189 102694957).card = 112 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 102662189 102694957
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 102694957 102727725 = 126 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 102694957 102727725).card = 126 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 102694957 102727725
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 102727725 102760493 = 133 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 102727725 102760493).card = 133 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 102727725 102760493
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 102629421 102694957).card = 237 := by
  simpa using combineTwinPrimeSegments (by decide : 102629421 ≤ 102662189)
    (by decide : 102662189 ≤ 102694957) block0 block1

theorem join_0_1 : (twinPrimeSegment 102694957 102760493).card = 259 := by
  simpa using combineTwinPrimeSegments (by decide : 102694957 ≤ 102727725)
    (by decide : 102727725 ≤ 102760493) block2 block3

theorem join_1_0 : (twinPrimeSegment 102629421 102760493).card = 496 := by
  simpa using combineTwinPrimeSegments (by decide : 102629421 ≤ 102694957)
    (by decide : 102694957 ≤ 102760493) join_0_0 join_0_1

theorem total : (twinPrimeSegment 102629421 102760493).card = 496 := join_1_0

end S048C15
end Sude.GeneratedTwinScan
