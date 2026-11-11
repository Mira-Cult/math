import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinGeometricScan

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S026C00
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def widths0 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked0 : geometricActiveStreamingTwinScan finiteTwinCheckedBase 54525997 widths0 = 119 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 54525997 54558765).card = 119 := by
  have h := geometricActiveStreamingTwinScan_spec finiteTwinCheckedBase 32768 54525997 widths0
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [checked0] at h
  simpa [widths0] using h.symm

def widths1 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked1 : geometricActiveStreamingTwinScan finiteTwinCheckedBase 54558765 widths1 = 133 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 54558765 54591533).card = 133 := by
  have h := geometricActiveStreamingTwinScan_spec finiteTwinCheckedBase 32768 54558765 widths1
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [checked1] at h
  simpa [widths1] using h.symm

def widths2 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked2 : geometricActiveStreamingTwinScan finiteTwinCheckedBase 54591533 widths2 = 138 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 54591533 54624301).card = 138 := by
  have h := geometricActiveStreamingTwinScan_spec finiteTwinCheckedBase 32768 54591533 widths2
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [checked2] at h
  simpa [widths2] using h.symm

def widths3 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked3 : geometricActiveStreamingTwinScan finiteTwinCheckedBase 54624301 widths3 = 151 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 54624301 54657069).card = 151 := by
  have h := geometricActiveStreamingTwinScan_spec finiteTwinCheckedBase 32768 54624301 widths3
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [checked3] at h
  simpa [widths3] using h.symm

theorem join_0_0 : (twinPrimeSegment 54525997 54591533).card = 252 := by
  simpa using combineTwinPrimeSegments (by decide : 54525997 ≤ 54558765)
    (by decide : 54558765 ≤ 54591533) block0 block1

theorem join_0_1 : (twinPrimeSegment 54591533 54657069).card = 289 := by
  simpa using combineTwinPrimeSegments (by decide : 54591533 ≤ 54624301)
    (by decide : 54624301 ≤ 54657069) block2 block3

theorem join_1_0 : (twinPrimeSegment 54525997 54657069).card = 541 := by
  simpa using combineTwinPrimeSegments (by decide : 54525997 ≤ 54591533)
    (by decide : 54591533 ≤ 54657069) join_0_0 join_0_1

theorem total : (twinPrimeSegment 54525997 54657069).card = 541 := join_1_0

end S026C00
end Sude.GeneratedTwinScan
