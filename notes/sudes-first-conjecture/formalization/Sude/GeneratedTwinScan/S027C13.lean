import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinGeometricScan

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S027C13
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def widths0 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked0 : geometricActiveStreamingTwinScan finiteTwinCheckedBase 58327085 widths0 = 139 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 58327085 58359853).card = 139 := by
  have h := geometricActiveStreamingTwinScan_spec finiteTwinCheckedBase 32768 58327085 widths0
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [checked0] at h
  simpa [widths0] using h.symm

def widths1 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked1 : geometricActiveStreamingTwinScan finiteTwinCheckedBase 58359853 widths1 = 147 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 58359853 58392621).card = 147 := by
  have h := geometricActiveStreamingTwinScan_spec finiteTwinCheckedBase 32768 58359853 widths1
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [checked1] at h
  simpa [widths1] using h.symm

def widths2 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked2 : geometricActiveStreamingTwinScan finiteTwinCheckedBase 58392621 widths2 = 123 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 58392621 58425389).card = 123 := by
  have h := geometricActiveStreamingTwinScan_spec finiteTwinCheckedBase 32768 58392621 widths2
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [checked2] at h
  simpa [widths2] using h.symm

def widths3 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked3 : geometricActiveStreamingTwinScan finiteTwinCheckedBase 58425389 widths3 = 125 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 58425389 58458157).card = 125 := by
  have h := geometricActiveStreamingTwinScan_spec finiteTwinCheckedBase 32768 58425389 widths3
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [checked3] at h
  simpa [widths3] using h.symm

theorem join_0_0 : (twinPrimeSegment 58327085 58392621).card = 286 := by
  simpa using combineTwinPrimeSegments (by decide : 58327085 ≤ 58359853)
    (by decide : 58359853 ≤ 58392621) block0 block1

theorem join_0_1 : (twinPrimeSegment 58392621 58458157).card = 248 := by
  simpa using combineTwinPrimeSegments (by decide : 58392621 ≤ 58425389)
    (by decide : 58425389 ≤ 58458157) block2 block3

theorem join_1_0 : (twinPrimeSegment 58327085 58458157).card = 534 := by
  simpa using combineTwinPrimeSegments (by decide : 58327085 ≤ 58392621)
    (by decide : 58392621 ≤ 58458157) join_0_0 join_0_1

theorem total : (twinPrimeSegment 58327085 58458157).card = 534 := join_1_0

end S027C13
end Sude.GeneratedTwinScan
