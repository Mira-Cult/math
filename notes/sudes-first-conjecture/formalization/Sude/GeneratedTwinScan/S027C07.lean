import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinGeometricScan

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S027C07
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def widths0 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked0 : geometricActiveStreamingTwinScan finiteTwinCheckedBase 57540653 widths0 = 114 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 57540653 57573421).card = 114 := by
  have h := geometricActiveStreamingTwinScan_spec finiteTwinCheckedBase 32768 57540653 widths0
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [checked0] at h
  simpa [widths0] using h.symm

def widths1 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked1 : geometricActiveStreamingTwinScan finiteTwinCheckedBase 57573421 widths1 = 137 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 57573421 57606189).card = 137 := by
  have h := geometricActiveStreamingTwinScan_spec finiteTwinCheckedBase 32768 57573421 widths1
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [checked1] at h
  simpa [widths1] using h.symm

def widths2 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked2 : geometricActiveStreamingTwinScan finiteTwinCheckedBase 57606189 widths2 = 149 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 57606189 57638957).card = 149 := by
  have h := geometricActiveStreamingTwinScan_spec finiteTwinCheckedBase 32768 57606189 widths2
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [checked2] at h
  simpa [widths2] using h.symm

def widths3 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked3 : geometricActiveStreamingTwinScan finiteTwinCheckedBase 57638957 widths3 = 122 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 57638957 57671725).card = 122 := by
  have h := geometricActiveStreamingTwinScan_spec finiteTwinCheckedBase 32768 57638957 widths3
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [checked3] at h
  simpa [widths3] using h.symm

theorem join_0_0 : (twinPrimeSegment 57540653 57606189).card = 251 := by
  simpa using combineTwinPrimeSegments (by decide : 57540653 ≤ 57573421)
    (by decide : 57573421 ≤ 57606189) block0 block1

theorem join_0_1 : (twinPrimeSegment 57606189 57671725).card = 271 := by
  simpa using combineTwinPrimeSegments (by decide : 57606189 ≤ 57638957)
    (by decide : 57638957 ≤ 57671725) block2 block3

theorem join_1_0 : (twinPrimeSegment 57540653 57671725).card = 522 := by
  simpa using combineTwinPrimeSegments (by decide : 57540653 ≤ 57606189)
    (by decide : 57606189 ≤ 57671725) join_0_0 join_0_1

theorem total : (twinPrimeSegment 57540653 57671725).card = 522 := join_1_0

end S027C07
end Sude.GeneratedTwinScan
