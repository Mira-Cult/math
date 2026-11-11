import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinGeometricScan

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S016C04
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def widths0 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked0 : geometricActiveStreamingTwinScan finiteTwinCheckedBase 34078765 widths0 = 147 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 34078765 34111533).card = 147 := by
  have h := geometricActiveStreamingTwinScan_spec finiteTwinCheckedBase 32768 34078765 widths0
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [checked0] at h
  simpa [widths0] using h.symm

def widths1 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked1 : geometricActiveStreamingTwinScan finiteTwinCheckedBase 34111533 widths1 = 165 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 34111533 34144301).card = 165 := by
  have h := geometricActiveStreamingTwinScan_spec finiteTwinCheckedBase 32768 34111533 widths1
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [checked1] at h
  simpa [widths1] using h.symm

def widths2 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked2 : geometricActiveStreamingTwinScan finiteTwinCheckedBase 34144301 widths2 = 129 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 34144301 34177069).card = 129 := by
  have h := geometricActiveStreamingTwinScan_spec finiteTwinCheckedBase 32768 34144301 widths2
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [checked2] at h
  simpa [widths2] using h.symm

def widths3 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked3 : geometricActiveStreamingTwinScan finiteTwinCheckedBase 34177069 widths3 = 138 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 34177069 34209837).card = 138 := by
  have h := geometricActiveStreamingTwinScan_spec finiteTwinCheckedBase 32768 34177069 widths3
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [checked3] at h
  simpa [widths3] using h.symm

theorem join_0_0 : (twinPrimeSegment 34078765 34144301).card = 312 := by
  simpa using combineTwinPrimeSegments (by decide : 34078765 ≤ 34111533)
    (by decide : 34111533 ≤ 34144301) block0 block1

theorem join_0_1 : (twinPrimeSegment 34144301 34209837).card = 267 := by
  simpa using combineTwinPrimeSegments (by decide : 34144301 ≤ 34177069)
    (by decide : 34177069 ≤ 34209837) block2 block3

theorem join_1_0 : (twinPrimeSegment 34078765 34209837).card = 579 := by
  simpa using combineTwinPrimeSegments (by decide : 34078765 ≤ 34144301)
    (by decide : 34144301 ≤ 34209837) join_0_0 join_0_1

theorem total : (twinPrimeSegment 34078765 34209837).card = 579 := join_1_0

end S016C04
end Sude.GeneratedTwinScan
