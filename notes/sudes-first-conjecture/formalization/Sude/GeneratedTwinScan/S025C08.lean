import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinGeometricScan

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S025C08
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def widths0 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked0 : geometricActiveStreamingTwinScan finiteTwinCheckedBase 53477421 widths0 = 132 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 53477421 53510189).card = 132 := by
  have h := geometricActiveStreamingTwinScan_spec finiteTwinCheckedBase 32768 53477421 widths0
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [checked0] at h
  simpa [widths0] using h.symm

def widths1 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked1 : geometricActiveStreamingTwinScan finiteTwinCheckedBase 53510189 widths1 = 134 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 53510189 53542957).card = 134 := by
  have h := geometricActiveStreamingTwinScan_spec finiteTwinCheckedBase 32768 53510189 widths1
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [checked1] at h
  simpa [widths1] using h.symm

def widths2 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked2 : geometricActiveStreamingTwinScan finiteTwinCheckedBase 53542957 widths2 = 123 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 53542957 53575725).card = 123 := by
  have h := geometricActiveStreamingTwinScan_spec finiteTwinCheckedBase 32768 53542957 widths2
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [checked2] at h
  simpa [widths2] using h.symm

def widths3 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked3 : geometricActiveStreamingTwinScan finiteTwinCheckedBase 53575725 widths3 = 141 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 53575725 53608493).card = 141 := by
  have h := geometricActiveStreamingTwinScan_spec finiteTwinCheckedBase 32768 53575725 widths3
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [checked3] at h
  simpa [widths3] using h.symm

theorem join_0_0 : (twinPrimeSegment 53477421 53542957).card = 266 := by
  simpa using combineTwinPrimeSegments (by decide : 53477421 ≤ 53510189)
    (by decide : 53510189 ≤ 53542957) block0 block1

theorem join_0_1 : (twinPrimeSegment 53542957 53608493).card = 264 := by
  simpa using combineTwinPrimeSegments (by decide : 53542957 ≤ 53575725)
    (by decide : 53575725 ≤ 53608493) block2 block3

theorem join_1_0 : (twinPrimeSegment 53477421 53608493).card = 530 := by
  simpa using combineTwinPrimeSegments (by decide : 53477421 ≤ 53542957)
    (by decide : 53542957 ≤ 53608493) join_0_0 join_0_1

theorem total : (twinPrimeSegment 53477421 53608493).card = 530 := join_1_0

end S025C08
end Sude.GeneratedTwinScan
