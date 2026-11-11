import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinGeometricScan

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S017C11
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def widths0 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked0 : geometricActiveStreamingTwinScan finiteTwinCheckedBase 37093421 widths0 = 163 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 37093421 37126189).card = 163 := by
  have h := geometricActiveStreamingTwinScan_spec finiteTwinCheckedBase 32768 37093421 widths0
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [checked0] at h
  simpa [widths0] using h.symm

def widths1 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked1 : geometricActiveStreamingTwinScan finiteTwinCheckedBase 37126189 widths1 = 144 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 37126189 37158957).card = 144 := by
  have h := geometricActiveStreamingTwinScan_spec finiteTwinCheckedBase 32768 37126189 widths1
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [checked1] at h
  simpa [widths1] using h.symm

def widths2 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked2 : geometricActiveStreamingTwinScan finiteTwinCheckedBase 37158957 widths2 = 132 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 37158957 37191725).card = 132 := by
  have h := geometricActiveStreamingTwinScan_spec finiteTwinCheckedBase 32768 37158957 widths2
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [checked2] at h
  simpa [widths2] using h.symm

def widths3 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked3 : geometricActiveStreamingTwinScan finiteTwinCheckedBase 37191725 widths3 = 144 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 37191725 37224493).card = 144 := by
  have h := geometricActiveStreamingTwinScan_spec finiteTwinCheckedBase 32768 37191725 widths3
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [checked3] at h
  simpa [widths3] using h.symm

theorem join_0_0 : (twinPrimeSegment 37093421 37158957).card = 307 := by
  simpa using combineTwinPrimeSegments (by decide : 37093421 ≤ 37126189)
    (by decide : 37126189 ≤ 37158957) block0 block1

theorem join_0_1 : (twinPrimeSegment 37158957 37224493).card = 276 := by
  simpa using combineTwinPrimeSegments (by decide : 37158957 ≤ 37191725)
    (by decide : 37191725 ≤ 37224493) block2 block3

theorem join_1_0 : (twinPrimeSegment 37093421 37224493).card = 583 := by
  simpa using combineTwinPrimeSegments (by decide : 37093421 ≤ 37158957)
    (by decide : 37158957 ≤ 37224493) join_0_0 join_0_1

theorem total : (twinPrimeSegment 37093421 37224493).card = 583 := join_1_0

end S017C11
end Sude.GeneratedTwinScan
