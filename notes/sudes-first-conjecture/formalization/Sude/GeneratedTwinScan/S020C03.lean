import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinGeometricScan

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S020C03
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def widths0 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked0 : geometricActiveStreamingTwinScan finiteTwinCheckedBase 42336301 widths0 = 135 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 42336301 42369069).card = 135 := by
  have h := geometricActiveStreamingTwinScan_spec finiteTwinCheckedBase 32768 42336301 widths0
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [checked0] at h
  simpa [widths0] using h.symm

def widths1 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked1 : geometricActiveStreamingTwinScan finiteTwinCheckedBase 42369069 widths1 = 142 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 42369069 42401837).card = 142 := by
  have h := geometricActiveStreamingTwinScan_spec finiteTwinCheckedBase 32768 42369069 widths1
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [checked1] at h
  simpa [widths1] using h.symm

def widths2 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked2 : geometricActiveStreamingTwinScan finiteTwinCheckedBase 42401837 widths2 = 125 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 42401837 42434605).card = 125 := by
  have h := geometricActiveStreamingTwinScan_spec finiteTwinCheckedBase 32768 42401837 widths2
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [checked2] at h
  simpa [widths2] using h.symm

def widths3 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked3 : geometricActiveStreamingTwinScan finiteTwinCheckedBase 42434605 widths3 = 124 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 42434605 42467373).card = 124 := by
  have h := geometricActiveStreamingTwinScan_spec finiteTwinCheckedBase 32768 42434605 widths3
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [checked3] at h
  simpa [widths3] using h.symm

theorem join_0_0 : (twinPrimeSegment 42336301 42401837).card = 277 := by
  simpa using combineTwinPrimeSegments (by decide : 42336301 ≤ 42369069)
    (by decide : 42369069 ≤ 42401837) block0 block1

theorem join_0_1 : (twinPrimeSegment 42401837 42467373).card = 249 := by
  simpa using combineTwinPrimeSegments (by decide : 42401837 ≤ 42434605)
    (by decide : 42434605 ≤ 42467373) block2 block3

theorem join_1_0 : (twinPrimeSegment 42336301 42467373).card = 526 := by
  simpa using combineTwinPrimeSegments (by decide : 42336301 ≤ 42401837)
    (by decide : 42401837 ≤ 42467373) join_0_0 join_0_1

theorem total : (twinPrimeSegment 42336301 42467373).card = 526 := join_1_0

end S020C03
end Sude.GeneratedTwinScan
