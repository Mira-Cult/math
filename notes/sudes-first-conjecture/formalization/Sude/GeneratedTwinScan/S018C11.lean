import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinGeometricScan

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S018C11
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def widths0 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked0 : geometricActiveStreamingTwinScan finiteTwinCheckedBase 39190573 widths0 = 133 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 39190573 39223341).card = 133 := by
  have h := geometricActiveStreamingTwinScan_spec finiteTwinCheckedBase 32768 39190573 widths0
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [checked0] at h
  simpa [widths0] using h.symm

def widths1 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked1 : geometricActiveStreamingTwinScan finiteTwinCheckedBase 39223341 widths1 = 153 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 39223341 39256109).card = 153 := by
  have h := geometricActiveStreamingTwinScan_spec finiteTwinCheckedBase 32768 39223341 widths1
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [checked1] at h
  simpa [widths1] using h.symm

def widths2 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked2 : geometricActiveStreamingTwinScan finiteTwinCheckedBase 39256109 widths2 = 132 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 39256109 39288877).card = 132 := by
  have h := geometricActiveStreamingTwinScan_spec finiteTwinCheckedBase 32768 39256109 widths2
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [checked2] at h
  simpa [widths2] using h.symm

def widths3 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked3 : geometricActiveStreamingTwinScan finiteTwinCheckedBase 39288877 widths3 = 136 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 39288877 39321645).card = 136 := by
  have h := geometricActiveStreamingTwinScan_spec finiteTwinCheckedBase 32768 39288877 widths3
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [checked3] at h
  simpa [widths3] using h.symm

theorem join_0_0 : (twinPrimeSegment 39190573 39256109).card = 286 := by
  simpa using combineTwinPrimeSegments (by decide : 39190573 ≤ 39223341)
    (by decide : 39223341 ≤ 39256109) block0 block1

theorem join_0_1 : (twinPrimeSegment 39256109 39321645).card = 268 := by
  simpa using combineTwinPrimeSegments (by decide : 39256109 ≤ 39288877)
    (by decide : 39288877 ≤ 39321645) block2 block3

theorem join_1_0 : (twinPrimeSegment 39190573 39321645).card = 554 := by
  simpa using combineTwinPrimeSegments (by decide : 39190573 ≤ 39256109)
    (by decide : 39256109 ≤ 39321645) join_0_0 join_0_1

theorem total : (twinPrimeSegment 39190573 39321645).card = 554 := join_1_0

end S018C11
end Sude.GeneratedTwinScan
