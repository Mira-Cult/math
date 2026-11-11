import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S048C09
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 101842989 101875757 = 148 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 101842989 101875757).card = 148 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 101842989 101875757
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 101875757 101908525 = 115 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 101875757 101908525).card = 115 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 101875757 101908525
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 101908525 101941293 = 133 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 101908525 101941293).card = 133 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 101908525 101941293
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 101941293 101974061 = 126 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 101941293 101974061).card = 126 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 101941293 101974061
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 101842989 101908525).card = 263 := by
  simpa using combineTwinPrimeSegments (by decide : 101842989 ≤ 101875757)
    (by decide : 101875757 ≤ 101908525) block0 block1

theorem join_0_1 : (twinPrimeSegment 101908525 101974061).card = 259 := by
  simpa using combineTwinPrimeSegments (by decide : 101908525 ≤ 101941293)
    (by decide : 101941293 ≤ 101974061) block2 block3

theorem join_1_0 : (twinPrimeSegment 101842989 101974061).card = 522 := by
  simpa using combineTwinPrimeSegments (by decide : 101842989 ≤ 101908525)
    (by decide : 101908525 ≤ 101974061) join_0_0 join_0_1

theorem total : (twinPrimeSegment 101842989 101974061).card = 522 := join_1_0

end S048C09
end Sude.GeneratedTwinScan
