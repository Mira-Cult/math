import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinGeometricScan

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S023C15
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def widths0 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked0 : geometricActiveStreamingTwinScan finiteTwinCheckedBase 50200621 widths0 = 133 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 50200621 50233389).card = 133 := by
  have h := geometricActiveStreamingTwinScan_spec finiteTwinCheckedBase 32768 50200621 widths0
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [checked0] at h
  simpa [widths0] using h.symm

def widths1 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked1 : geometricActiveStreamingTwinScan finiteTwinCheckedBase 50233389 widths1 = 126 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 50233389 50266157).card = 126 := by
  have h := geometricActiveStreamingTwinScan_spec finiteTwinCheckedBase 32768 50233389 widths1
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [checked1] at h
  simpa [widths1] using h.symm

def widths2 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked2 : geometricActiveStreamingTwinScan finiteTwinCheckedBase 50266157 widths2 = 118 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 50266157 50298925).card = 118 := by
  have h := geometricActiveStreamingTwinScan_spec finiteTwinCheckedBase 32768 50266157 widths2
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [checked2] at h
  simpa [widths2] using h.symm

def widths3 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked3 : geometricActiveStreamingTwinScan finiteTwinCheckedBase 50298925 widths3 = 135 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 50298925 50331693).card = 135 := by
  have h := geometricActiveStreamingTwinScan_spec finiteTwinCheckedBase 32768 50298925 widths3
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [checked3] at h
  simpa [widths3] using h.symm

theorem join_0_0 : (twinPrimeSegment 50200621 50266157).card = 259 := by
  simpa using combineTwinPrimeSegments (by decide : 50200621 ≤ 50233389)
    (by decide : 50233389 ≤ 50266157) block0 block1

theorem join_0_1 : (twinPrimeSegment 50266157 50331693).card = 253 := by
  simpa using combineTwinPrimeSegments (by decide : 50266157 ≤ 50298925)
    (by decide : 50298925 ≤ 50331693) block2 block3

theorem join_1_0 : (twinPrimeSegment 50200621 50331693).card = 512 := by
  simpa using combineTwinPrimeSegments (by decide : 50200621 ≤ 50266157)
    (by decide : 50266157 ≤ 50331693) join_0_0 join_0_1

theorem total : (twinPrimeSegment 50200621 50331693).card = 512 := join_1_0

end S023C15
end Sude.GeneratedTwinScan
