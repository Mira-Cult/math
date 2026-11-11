import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinGeometricScan

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S023C08
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def widths0 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked0 : geometricActiveStreamingTwinScan finiteTwinCheckedBase 49283117 widths0 = 124 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 49283117 49315885).card = 124 := by
  have h := geometricActiveStreamingTwinScan_spec finiteTwinCheckedBase 32768 49283117 widths0
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [checked0] at h
  simpa [widths0] using h.symm

def widths1 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked1 : geometricActiveStreamingTwinScan finiteTwinCheckedBase 49315885 widths1 = 137 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 49315885 49348653).card = 137 := by
  have h := geometricActiveStreamingTwinScan_spec finiteTwinCheckedBase 32768 49315885 widths1
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [checked1] at h
  simpa [widths1] using h.symm

def widths2 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked2 : geometricActiveStreamingTwinScan finiteTwinCheckedBase 49348653 widths2 = 152 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 49348653 49381421).card = 152 := by
  have h := geometricActiveStreamingTwinScan_spec finiteTwinCheckedBase 32768 49348653 widths2
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [checked2] at h
  simpa [widths2] using h.symm

def widths3 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked3 : geometricActiveStreamingTwinScan finiteTwinCheckedBase 49381421 widths3 = 148 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 49381421 49414189).card = 148 := by
  have h := geometricActiveStreamingTwinScan_spec finiteTwinCheckedBase 32768 49381421 widths3
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [checked3] at h
  simpa [widths3] using h.symm

theorem join_0_0 : (twinPrimeSegment 49283117 49348653).card = 261 := by
  simpa using combineTwinPrimeSegments (by decide : 49283117 ≤ 49315885)
    (by decide : 49315885 ≤ 49348653) block0 block1

theorem join_0_1 : (twinPrimeSegment 49348653 49414189).card = 300 := by
  simpa using combineTwinPrimeSegments (by decide : 49348653 ≤ 49381421)
    (by decide : 49381421 ≤ 49414189) block2 block3

theorem join_1_0 : (twinPrimeSegment 49283117 49414189).card = 561 := by
  simpa using combineTwinPrimeSegments (by decide : 49283117 ≤ 49348653)
    (by decide : 49348653 ≤ 49414189) join_0_0 join_0_1

theorem total : (twinPrimeSegment 49283117 49414189).card = 561 := join_1_0

end S023C08
end Sude.GeneratedTwinScan
