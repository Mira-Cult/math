import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinGeometricScan

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S017C15
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def widths0 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked0 : geometricActiveStreamingTwinScan finiteTwinCheckedBase 37617709 widths0 = 128 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 37617709 37650477).card = 128 := by
  have h := geometricActiveStreamingTwinScan_spec finiteTwinCheckedBase 32768 37617709 widths0
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [checked0] at h
  simpa [widths0] using h.symm

def widths1 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked1 : geometricActiveStreamingTwinScan finiteTwinCheckedBase 37650477 widths1 = 149 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 37650477 37683245).card = 149 := by
  have h := geometricActiveStreamingTwinScan_spec finiteTwinCheckedBase 32768 37650477 widths1
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [checked1] at h
  simpa [widths1] using h.symm

def widths2 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked2 : geometricActiveStreamingTwinScan finiteTwinCheckedBase 37683245 widths2 = 128 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 37683245 37716013).card = 128 := by
  have h := geometricActiveStreamingTwinScan_spec finiteTwinCheckedBase 32768 37683245 widths2
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [checked2] at h
  simpa [widths2] using h.symm

def widths3 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked3 : geometricActiveStreamingTwinScan finiteTwinCheckedBase 37716013 widths3 = 141 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 37716013 37748781).card = 141 := by
  have h := geometricActiveStreamingTwinScan_spec finiteTwinCheckedBase 32768 37716013 widths3
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [checked3] at h
  simpa [widths3] using h.symm

theorem join_0_0 : (twinPrimeSegment 37617709 37683245).card = 277 := by
  simpa using combineTwinPrimeSegments (by decide : 37617709 ≤ 37650477)
    (by decide : 37650477 ≤ 37683245) block0 block1

theorem join_0_1 : (twinPrimeSegment 37683245 37748781).card = 269 := by
  simpa using combineTwinPrimeSegments (by decide : 37683245 ≤ 37716013)
    (by decide : 37716013 ≤ 37748781) block2 block3

theorem join_1_0 : (twinPrimeSegment 37617709 37748781).card = 546 := by
  simpa using combineTwinPrimeSegments (by decide : 37617709 ≤ 37683245)
    (by decide : 37683245 ≤ 37748781) join_0_0 join_0_1

theorem total : (twinPrimeSegment 37617709 37748781).card = 546 := join_1_0

end S017C15
end Sude.GeneratedTwinScan
