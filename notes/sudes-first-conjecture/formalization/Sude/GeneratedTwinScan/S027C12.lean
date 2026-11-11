import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinGeometricScan

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S027C12
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def widths0 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked0 : geometricActiveStreamingTwinScan finiteTwinCheckedBase 58196013 widths0 = 163 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 58196013 58228781).card = 163 := by
  have h := geometricActiveStreamingTwinScan_spec finiteTwinCheckedBase 32768 58196013 widths0
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [checked0] at h
  simpa [widths0] using h.symm

def widths1 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked1 : geometricActiveStreamingTwinScan finiteTwinCheckedBase 58228781 widths1 = 126 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 58228781 58261549).card = 126 := by
  have h := geometricActiveStreamingTwinScan_spec finiteTwinCheckedBase 32768 58228781 widths1
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [checked1] at h
  simpa [widths1] using h.symm

def widths2 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked2 : geometricActiveStreamingTwinScan finiteTwinCheckedBase 58261549 widths2 = 133 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 58261549 58294317).card = 133 := by
  have h := geometricActiveStreamingTwinScan_spec finiteTwinCheckedBase 32768 58261549 widths2
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [checked2] at h
  simpa [widths2] using h.symm

def widths3 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked3 : geometricActiveStreamingTwinScan finiteTwinCheckedBase 58294317 widths3 = 127 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 58294317 58327085).card = 127 := by
  have h := geometricActiveStreamingTwinScan_spec finiteTwinCheckedBase 32768 58294317 widths3
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [checked3] at h
  simpa [widths3] using h.symm

theorem join_0_0 : (twinPrimeSegment 58196013 58261549).card = 289 := by
  simpa using combineTwinPrimeSegments (by decide : 58196013 ≤ 58228781)
    (by decide : 58228781 ≤ 58261549) block0 block1

theorem join_0_1 : (twinPrimeSegment 58261549 58327085).card = 260 := by
  simpa using combineTwinPrimeSegments (by decide : 58261549 ≤ 58294317)
    (by decide : 58294317 ≤ 58327085) block2 block3

theorem join_1_0 : (twinPrimeSegment 58196013 58327085).card = 549 := by
  simpa using combineTwinPrimeSegments (by decide : 58196013 ≤ 58261549)
    (by decide : 58261549 ≤ 58327085) join_0_0 join_0_1

theorem total : (twinPrimeSegment 58196013 58327085).card = 549 := join_1_0

end S027C12
end Sude.GeneratedTwinScan
