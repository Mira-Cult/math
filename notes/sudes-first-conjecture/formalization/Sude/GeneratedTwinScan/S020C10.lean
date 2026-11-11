import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinGeometricScan

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S020C10
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def widths0 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked0 : geometricActiveStreamingTwinScan finiteTwinCheckedBase 43253805 widths0 = 148 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 43253805 43286573).card = 148 := by
  have h := geometricActiveStreamingTwinScan_spec finiteTwinCheckedBase 32768 43253805 widths0
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [checked0] at h
  simpa [widths0] using h.symm

def widths1 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked1 : geometricActiveStreamingTwinScan finiteTwinCheckedBase 43286573 widths1 = 153 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 43286573 43319341).card = 153 := by
  have h := geometricActiveStreamingTwinScan_spec finiteTwinCheckedBase 32768 43286573 widths1
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [checked1] at h
  simpa [widths1] using h.symm

def widths2 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked2 : geometricActiveStreamingTwinScan finiteTwinCheckedBase 43319341 widths2 = 126 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 43319341 43352109).card = 126 := by
  have h := geometricActiveStreamingTwinScan_spec finiteTwinCheckedBase 32768 43319341 widths2
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [checked2] at h
  simpa [widths2] using h.symm

def widths3 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked3 : geometricActiveStreamingTwinScan finiteTwinCheckedBase 43352109 widths3 = 134 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 43352109 43384877).card = 134 := by
  have h := geometricActiveStreamingTwinScan_spec finiteTwinCheckedBase 32768 43352109 widths3
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [checked3] at h
  simpa [widths3] using h.symm

theorem join_0_0 : (twinPrimeSegment 43253805 43319341).card = 301 := by
  simpa using combineTwinPrimeSegments (by decide : 43253805 ≤ 43286573)
    (by decide : 43286573 ≤ 43319341) block0 block1

theorem join_0_1 : (twinPrimeSegment 43319341 43384877).card = 260 := by
  simpa using combineTwinPrimeSegments (by decide : 43319341 ≤ 43352109)
    (by decide : 43352109 ≤ 43384877) block2 block3

theorem join_1_0 : (twinPrimeSegment 43253805 43384877).card = 561 := by
  simpa using combineTwinPrimeSegments (by decide : 43253805 ≤ 43319341)
    (by decide : 43319341 ≤ 43384877) join_0_0 join_0_1

theorem total : (twinPrimeSegment 43253805 43384877).card = 561 := join_1_0

end S020C10
end Sude.GeneratedTwinScan
