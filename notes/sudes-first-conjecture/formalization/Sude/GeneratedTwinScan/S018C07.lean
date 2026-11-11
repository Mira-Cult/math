import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinGeometricScan

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S018C07
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def widths0 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked0 : geometricActiveStreamingTwinScan finiteTwinCheckedBase 38666285 widths0 = 155 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 38666285 38699053).card = 155 := by
  have h := geometricActiveStreamingTwinScan_spec finiteTwinCheckedBase 32768 38666285 widths0
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [checked0] at h
  simpa [widths0] using h.symm

def widths1 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked1 : geometricActiveStreamingTwinScan finiteTwinCheckedBase 38699053 widths1 = 147 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 38699053 38731821).card = 147 := by
  have h := geometricActiveStreamingTwinScan_spec finiteTwinCheckedBase 32768 38699053 widths1
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [checked1] at h
  simpa [widths1] using h.symm

def widths2 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked2 : geometricActiveStreamingTwinScan finiteTwinCheckedBase 38731821 widths2 = 140 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 38731821 38764589).card = 140 := by
  have h := geometricActiveStreamingTwinScan_spec finiteTwinCheckedBase 32768 38731821 widths2
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [checked2] at h
  simpa [widths2] using h.symm

def widths3 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked3 : geometricActiveStreamingTwinScan finiteTwinCheckedBase 38764589 widths3 = 153 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 38764589 38797357).card = 153 := by
  have h := geometricActiveStreamingTwinScan_spec finiteTwinCheckedBase 32768 38764589 widths3
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [checked3] at h
  simpa [widths3] using h.symm

theorem join_0_0 : (twinPrimeSegment 38666285 38731821).card = 302 := by
  simpa using combineTwinPrimeSegments (by decide : 38666285 ≤ 38699053)
    (by decide : 38699053 ≤ 38731821) block0 block1

theorem join_0_1 : (twinPrimeSegment 38731821 38797357).card = 293 := by
  simpa using combineTwinPrimeSegments (by decide : 38731821 ≤ 38764589)
    (by decide : 38764589 ≤ 38797357) block2 block3

theorem join_1_0 : (twinPrimeSegment 38666285 38797357).card = 595 := by
  simpa using combineTwinPrimeSegments (by decide : 38666285 ≤ 38731821)
    (by decide : 38731821 ≤ 38797357) join_0_0 join_0_1

theorem total : (twinPrimeSegment 38666285 38797357).card = 595 := join_1_0

end S018C07
end Sude.GeneratedTwinScan
