import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinGeometricScan

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S021C01
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def widths0 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked0 : geometricActiveStreamingTwinScan finiteTwinCheckedBase 44171309 widths0 = 146 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 44171309 44204077).card = 146 := by
  have h := geometricActiveStreamingTwinScan_spec finiteTwinCheckedBase 32768 44171309 widths0
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [checked0] at h
  simpa [widths0] using h.symm

def widths1 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked1 : geometricActiveStreamingTwinScan finiteTwinCheckedBase 44204077 widths1 = 131 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 44204077 44236845).card = 131 := by
  have h := geometricActiveStreamingTwinScan_spec finiteTwinCheckedBase 32768 44204077 widths1
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [checked1] at h
  simpa [widths1] using h.symm

def widths2 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked2 : geometricActiveStreamingTwinScan finiteTwinCheckedBase 44236845 widths2 = 152 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 44236845 44269613).card = 152 := by
  have h := geometricActiveStreamingTwinScan_spec finiteTwinCheckedBase 32768 44236845 widths2
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [checked2] at h
  simpa [widths2] using h.symm

def widths3 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked3 : geometricActiveStreamingTwinScan finiteTwinCheckedBase 44269613 widths3 = 155 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 44269613 44302381).card = 155 := by
  have h := geometricActiveStreamingTwinScan_spec finiteTwinCheckedBase 32768 44269613 widths3
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [checked3] at h
  simpa [widths3] using h.symm

theorem join_0_0 : (twinPrimeSegment 44171309 44236845).card = 277 := by
  simpa using combineTwinPrimeSegments (by decide : 44171309 ≤ 44204077)
    (by decide : 44204077 ≤ 44236845) block0 block1

theorem join_0_1 : (twinPrimeSegment 44236845 44302381).card = 307 := by
  simpa using combineTwinPrimeSegments (by decide : 44236845 ≤ 44269613)
    (by decide : 44269613 ≤ 44302381) block2 block3

theorem join_1_0 : (twinPrimeSegment 44171309 44302381).card = 584 := by
  simpa using combineTwinPrimeSegments (by decide : 44171309 ≤ 44236845)
    (by decide : 44236845 ≤ 44302381) join_0_0 join_0_1

theorem total : (twinPrimeSegment 44171309 44302381).card = 584 := join_1_0

end S021C01
end Sude.GeneratedTwinScan
