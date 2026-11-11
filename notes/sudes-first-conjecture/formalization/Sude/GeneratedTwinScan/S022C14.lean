import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinGeometricScan

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S022C14
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def widths0 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked0 : geometricActiveStreamingTwinScan finiteTwinCheckedBase 47972397 widths0 = 122 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 47972397 48005165).card = 122 := by
  have h := geometricActiveStreamingTwinScan_spec finiteTwinCheckedBase 32768 47972397 widths0
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [checked0] at h
  simpa [widths0] using h.symm

def widths1 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked1 : geometricActiveStreamingTwinScan finiteTwinCheckedBase 48005165 widths1 = 149 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 48005165 48037933).card = 149 := by
  have h := geometricActiveStreamingTwinScan_spec finiteTwinCheckedBase 32768 48005165 widths1
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [checked1] at h
  simpa [widths1] using h.symm

def widths2 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked2 : geometricActiveStreamingTwinScan finiteTwinCheckedBase 48037933 widths2 = 125 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 48037933 48070701).card = 125 := by
  have h := geometricActiveStreamingTwinScan_spec finiteTwinCheckedBase 32768 48037933 widths2
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [checked2] at h
  simpa [widths2] using h.symm

def widths3 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked3 : geometricActiveStreamingTwinScan finiteTwinCheckedBase 48070701 widths3 = 143 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 48070701 48103469).card = 143 := by
  have h := geometricActiveStreamingTwinScan_spec finiteTwinCheckedBase 32768 48070701 widths3
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [checked3] at h
  simpa [widths3] using h.symm

theorem join_0_0 : (twinPrimeSegment 47972397 48037933).card = 271 := by
  simpa using combineTwinPrimeSegments (by decide : 47972397 ≤ 48005165)
    (by decide : 48005165 ≤ 48037933) block0 block1

theorem join_0_1 : (twinPrimeSegment 48037933 48103469).card = 268 := by
  simpa using combineTwinPrimeSegments (by decide : 48037933 ≤ 48070701)
    (by decide : 48070701 ≤ 48103469) block2 block3

theorem join_1_0 : (twinPrimeSegment 47972397 48103469).card = 539 := by
  simpa using combineTwinPrimeSegments (by decide : 47972397 ≤ 48037933)
    (by decide : 48037933 ≤ 48103469) join_0_0 join_0_1

theorem total : (twinPrimeSegment 47972397 48103469).card = 539 := join_1_0

end S022C14
end Sude.GeneratedTwinScan
