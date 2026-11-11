import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinGeometricScan

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S025C12
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def widths0 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked0 : geometricActiveStreamingTwinScan finiteTwinCheckedBase 54001709 widths0 = 125 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 54001709 54034477).card = 125 := by
  have h := geometricActiveStreamingTwinScan_spec finiteTwinCheckedBase 32768 54001709 widths0
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [checked0] at h
  simpa [widths0] using h.symm

def widths1 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked1 : geometricActiveStreamingTwinScan finiteTwinCheckedBase 54034477 widths1 = 141 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 54034477 54067245).card = 141 := by
  have h := geometricActiveStreamingTwinScan_spec finiteTwinCheckedBase 32768 54034477 widths1
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [checked1] at h
  simpa [widths1] using h.symm

def widths2 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked2 : geometricActiveStreamingTwinScan finiteTwinCheckedBase 54067245 widths2 = 146 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 54067245 54100013).card = 146 := by
  have h := geometricActiveStreamingTwinScan_spec finiteTwinCheckedBase 32768 54067245 widths2
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [checked2] at h
  simpa [widths2] using h.symm

def widths3 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked3 : geometricActiveStreamingTwinScan finiteTwinCheckedBase 54100013 widths3 = 142 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 54100013 54132781).card = 142 := by
  have h := geometricActiveStreamingTwinScan_spec finiteTwinCheckedBase 32768 54100013 widths3
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [checked3] at h
  simpa [widths3] using h.symm

theorem join_0_0 : (twinPrimeSegment 54001709 54067245).card = 266 := by
  simpa using combineTwinPrimeSegments (by decide : 54001709 ≤ 54034477)
    (by decide : 54034477 ≤ 54067245) block0 block1

theorem join_0_1 : (twinPrimeSegment 54067245 54132781).card = 288 := by
  simpa using combineTwinPrimeSegments (by decide : 54067245 ≤ 54100013)
    (by decide : 54100013 ≤ 54132781) block2 block3

theorem join_1_0 : (twinPrimeSegment 54001709 54132781).card = 554 := by
  simpa using combineTwinPrimeSegments (by decide : 54001709 ≤ 54067245)
    (by decide : 54067245 ≤ 54132781) join_0_0 join_0_1

theorem total : (twinPrimeSegment 54001709 54132781).card = 554 := join_1_0

end S025C12
end Sude.GeneratedTwinScan
