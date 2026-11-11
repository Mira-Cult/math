import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinGeometricScan

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S017C10
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def widths0 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked0 : geometricActiveStreamingTwinScan finiteTwinCheckedBase 36962349 widths0 = 168 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 36962349 36995117).card = 168 := by
  have h := geometricActiveStreamingTwinScan_spec finiteTwinCheckedBase 32768 36962349 widths0
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [checked0] at h
  simpa [widths0] using h.symm

def widths1 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked1 : geometricActiveStreamingTwinScan finiteTwinCheckedBase 36995117 widths1 = 147 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 36995117 37027885).card = 147 := by
  have h := geometricActiveStreamingTwinScan_spec finiteTwinCheckedBase 32768 36995117 widths1
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [checked1] at h
  simpa [widths1] using h.symm

def widths2 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked2 : geometricActiveStreamingTwinScan finiteTwinCheckedBase 37027885 widths2 = 138 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 37027885 37060653).card = 138 := by
  have h := geometricActiveStreamingTwinScan_spec finiteTwinCheckedBase 32768 37027885 widths2
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [checked2] at h
  simpa [widths2] using h.symm

def widths3 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked3 : geometricActiveStreamingTwinScan finiteTwinCheckedBase 37060653 widths3 = 147 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 37060653 37093421).card = 147 := by
  have h := geometricActiveStreamingTwinScan_spec finiteTwinCheckedBase 32768 37060653 widths3
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [checked3] at h
  simpa [widths3] using h.symm

theorem join_0_0 : (twinPrimeSegment 36962349 37027885).card = 315 := by
  simpa using combineTwinPrimeSegments (by decide : 36962349 ≤ 36995117)
    (by decide : 36995117 ≤ 37027885) block0 block1

theorem join_0_1 : (twinPrimeSegment 37027885 37093421).card = 285 := by
  simpa using combineTwinPrimeSegments (by decide : 37027885 ≤ 37060653)
    (by decide : 37060653 ≤ 37093421) block2 block3

theorem join_1_0 : (twinPrimeSegment 36962349 37093421).card = 600 := by
  simpa using combineTwinPrimeSegments (by decide : 36962349 ≤ 37027885)
    (by decide : 37027885 ≤ 37093421) join_0_0 join_0_1

theorem total : (twinPrimeSegment 36962349 37093421).card = 600 := join_1_0

end S017C10
end Sude.GeneratedTwinScan
