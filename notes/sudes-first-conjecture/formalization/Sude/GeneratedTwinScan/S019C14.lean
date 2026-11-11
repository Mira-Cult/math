import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinGeometricScan

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S019C14
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def widths0 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked0 : geometricActiveStreamingTwinScan finiteTwinCheckedBase 41680941 widths0 = 134 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 41680941 41713709).card = 134 := by
  have h := geometricActiveStreamingTwinScan_spec finiteTwinCheckedBase 32768 41680941 widths0
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [checked0] at h
  simpa [widths0] using h.symm

def widths1 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked1 : geometricActiveStreamingTwinScan finiteTwinCheckedBase 41713709 widths1 = 146 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 41713709 41746477).card = 146 := by
  have h := geometricActiveStreamingTwinScan_spec finiteTwinCheckedBase 32768 41713709 widths1
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [checked1] at h
  simpa [widths1] using h.symm

def widths2 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked2 : geometricActiveStreamingTwinScan finiteTwinCheckedBase 41746477 widths2 = 147 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 41746477 41779245).card = 147 := by
  have h := geometricActiveStreamingTwinScan_spec finiteTwinCheckedBase 32768 41746477 widths2
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [checked2] at h
  simpa [widths2] using h.symm

def widths3 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked3 : geometricActiveStreamingTwinScan finiteTwinCheckedBase 41779245 widths3 = 146 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 41779245 41812013).card = 146 := by
  have h := geometricActiveStreamingTwinScan_spec finiteTwinCheckedBase 32768 41779245 widths3
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [checked3] at h
  simpa [widths3] using h.symm

theorem join_0_0 : (twinPrimeSegment 41680941 41746477).card = 280 := by
  simpa using combineTwinPrimeSegments (by decide : 41680941 ≤ 41713709)
    (by decide : 41713709 ≤ 41746477) block0 block1

theorem join_0_1 : (twinPrimeSegment 41746477 41812013).card = 293 := by
  simpa using combineTwinPrimeSegments (by decide : 41746477 ≤ 41779245)
    (by decide : 41779245 ≤ 41812013) block2 block3

theorem join_1_0 : (twinPrimeSegment 41680941 41812013).card = 573 := by
  simpa using combineTwinPrimeSegments (by decide : 41680941 ≤ 41746477)
    (by decide : 41746477 ≤ 41812013) join_0_0 join_0_1

theorem total : (twinPrimeSegment 41680941 41812013).card = 573 := join_1_0

end S019C14
end Sude.GeneratedTwinScan
