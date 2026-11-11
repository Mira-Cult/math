import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinGeometricScan

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S019C10
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def widths0 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked0 : geometricActiveStreamingTwinScan finiteTwinCheckedBase 41156653 widths0 = 137 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 41156653 41189421).card = 137 := by
  have h := geometricActiveStreamingTwinScan_spec finiteTwinCheckedBase 32768 41156653 widths0
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [checked0] at h
  simpa [widths0] using h.symm

def widths1 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked1 : geometricActiveStreamingTwinScan finiteTwinCheckedBase 41189421 widths1 = 133 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 41189421 41222189).card = 133 := by
  have h := geometricActiveStreamingTwinScan_spec finiteTwinCheckedBase 32768 41189421 widths1
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [checked1] at h
  simpa [widths1] using h.symm

def widths2 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked2 : geometricActiveStreamingTwinScan finiteTwinCheckedBase 41222189 widths2 = 135 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 41222189 41254957).card = 135 := by
  have h := geometricActiveStreamingTwinScan_spec finiteTwinCheckedBase 32768 41222189 widths2
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [checked2] at h
  simpa [widths2] using h.symm

def widths3 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked3 : geometricActiveStreamingTwinScan finiteTwinCheckedBase 41254957 widths3 = 148 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 41254957 41287725).card = 148 := by
  have h := geometricActiveStreamingTwinScan_spec finiteTwinCheckedBase 32768 41254957 widths3
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [checked3] at h
  simpa [widths3] using h.symm

theorem join_0_0 : (twinPrimeSegment 41156653 41222189).card = 270 := by
  simpa using combineTwinPrimeSegments (by decide : 41156653 ≤ 41189421)
    (by decide : 41189421 ≤ 41222189) block0 block1

theorem join_0_1 : (twinPrimeSegment 41222189 41287725).card = 283 := by
  simpa using combineTwinPrimeSegments (by decide : 41222189 ≤ 41254957)
    (by decide : 41254957 ≤ 41287725) block2 block3

theorem join_1_0 : (twinPrimeSegment 41156653 41287725).card = 553 := by
  simpa using combineTwinPrimeSegments (by decide : 41156653 ≤ 41222189)
    (by decide : 41222189 ≤ 41287725) join_0_0 join_0_1

theorem total : (twinPrimeSegment 41156653 41287725).card = 553 := join_1_0

end S019C10
end Sude.GeneratedTwinScan
