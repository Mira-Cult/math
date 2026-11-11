import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S032C15
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 69074989 69107757 = 149 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 69074989 69107757).card = 149 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 69074989 69107757
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 69107757 69140525 = 148 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 69107757 69140525).card = 148 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 69107757 69140525
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 69140525 69173293 = 118 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 69140525 69173293).card = 118 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 69140525 69173293
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 69173293 69206061 = 126 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 69173293 69206061).card = 126 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 69173293 69206061
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 69074989 69140525).card = 297 := by
  simpa using combineTwinPrimeSegments (by decide : 69074989 ≤ 69107757)
    (by decide : 69107757 ≤ 69140525) block0 block1

theorem join_0_1 : (twinPrimeSegment 69140525 69206061).card = 244 := by
  simpa using combineTwinPrimeSegments (by decide : 69140525 ≤ 69173293)
    (by decide : 69173293 ≤ 69206061) block2 block3

theorem join_1_0 : (twinPrimeSegment 69074989 69206061).card = 541 := by
  simpa using combineTwinPrimeSegments (by decide : 69074989 ≤ 69140525)
    (by decide : 69140525 ≤ 69206061) join_0_0 join_0_1

theorem total : (twinPrimeSegment 69074989 69206061).card = 541 := join_1_0

end S032C15
end Sude.GeneratedTwinScan
