import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinGeometricScan

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S021C08
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def widths0 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked0 : geometricActiveStreamingTwinScan finiteTwinCheckedBase 45088813 widths0 = 152 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 45088813 45121581).card = 152 := by
  have h := geometricActiveStreamingTwinScan_spec finiteTwinCheckedBase 32768 45088813 widths0
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [checked0] at h
  simpa [widths0] using h.symm

def widths1 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked1 : geometricActiveStreamingTwinScan finiteTwinCheckedBase 45121581 widths1 = 122 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 45121581 45154349).card = 122 := by
  have h := geometricActiveStreamingTwinScan_spec finiteTwinCheckedBase 32768 45121581 widths1
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [checked1] at h
  simpa [widths1] using h.symm

def widths2 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked2 : geometricActiveStreamingTwinScan finiteTwinCheckedBase 45154349 widths2 = 130 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 45154349 45187117).card = 130 := by
  have h := geometricActiveStreamingTwinScan_spec finiteTwinCheckedBase 32768 45154349 widths2
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [checked2] at h
  simpa [widths2] using h.symm

def widths3 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked3 : geometricActiveStreamingTwinScan finiteTwinCheckedBase 45187117 widths3 = 132 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 45187117 45219885).card = 132 := by
  have h := geometricActiveStreamingTwinScan_spec finiteTwinCheckedBase 32768 45187117 widths3
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [checked3] at h
  simpa [widths3] using h.symm

theorem join_0_0 : (twinPrimeSegment 45088813 45154349).card = 274 := by
  simpa using combineTwinPrimeSegments (by decide : 45088813 ≤ 45121581)
    (by decide : 45121581 ≤ 45154349) block0 block1

theorem join_0_1 : (twinPrimeSegment 45154349 45219885).card = 262 := by
  simpa using combineTwinPrimeSegments (by decide : 45154349 ≤ 45187117)
    (by decide : 45187117 ≤ 45219885) block2 block3

theorem join_1_0 : (twinPrimeSegment 45088813 45219885).card = 536 := by
  simpa using combineTwinPrimeSegments (by decide : 45088813 ≤ 45154349)
    (by decide : 45154349 ≤ 45219885) join_0_0 join_0_1

theorem total : (twinPrimeSegment 45088813 45219885).card = 536 := join_1_0

end S021C08
end Sude.GeneratedTwinScan
