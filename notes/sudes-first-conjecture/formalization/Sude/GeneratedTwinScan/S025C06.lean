import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinGeometricScan

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S025C06
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def widths0 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked0 : geometricActiveStreamingTwinScan finiteTwinCheckedBase 53215277 widths0 = 149 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 53215277 53248045).card = 149 := by
  have h := geometricActiveStreamingTwinScan_spec finiteTwinCheckedBase 32768 53215277 widths0
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [checked0] at h
  simpa [widths0] using h.symm

def widths1 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked1 : geometricActiveStreamingTwinScan finiteTwinCheckedBase 53248045 widths1 = 134 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 53248045 53280813).card = 134 := by
  have h := geometricActiveStreamingTwinScan_spec finiteTwinCheckedBase 32768 53248045 widths1
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [checked1] at h
  simpa [widths1] using h.symm

def widths2 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked2 : geometricActiveStreamingTwinScan finiteTwinCheckedBase 53280813 widths2 = 129 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 53280813 53313581).card = 129 := by
  have h := geometricActiveStreamingTwinScan_spec finiteTwinCheckedBase 32768 53280813 widths2
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [checked2] at h
  simpa [widths2] using h.symm

def widths3 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked3 : geometricActiveStreamingTwinScan finiteTwinCheckedBase 53313581 widths3 = 142 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 53313581 53346349).card = 142 := by
  have h := geometricActiveStreamingTwinScan_spec finiteTwinCheckedBase 32768 53313581 widths3
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [checked3] at h
  simpa [widths3] using h.symm

theorem join_0_0 : (twinPrimeSegment 53215277 53280813).card = 283 := by
  simpa using combineTwinPrimeSegments (by decide : 53215277 ≤ 53248045)
    (by decide : 53248045 ≤ 53280813) block0 block1

theorem join_0_1 : (twinPrimeSegment 53280813 53346349).card = 271 := by
  simpa using combineTwinPrimeSegments (by decide : 53280813 ≤ 53313581)
    (by decide : 53313581 ≤ 53346349) block2 block3

theorem join_1_0 : (twinPrimeSegment 53215277 53346349).card = 554 := by
  simpa using combineTwinPrimeSegments (by decide : 53215277 ≤ 53280813)
    (by decide : 53280813 ≤ 53346349) join_0_0 join_0_1

theorem total : (twinPrimeSegment 53215277 53346349).card = 554 := join_1_0

end S025C06
end Sude.GeneratedTwinScan
