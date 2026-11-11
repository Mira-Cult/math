import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinGeometricScan

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S015C08
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def widths0 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked0 : geometricActiveStreamingTwinScan finiteTwinCheckedBase 32505901 widths0 = 127 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 32505901 32538669).card = 127 := by
  have h := geometricActiveStreamingTwinScan_spec finiteTwinCheckedBase 32768 32505901 widths0
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [checked0] at h
  simpa [widths0] using h.symm

def widths1 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked1 : geometricActiveStreamingTwinScan finiteTwinCheckedBase 32538669 widths1 = 126 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 32538669 32571437).card = 126 := by
  have h := geometricActiveStreamingTwinScan_spec finiteTwinCheckedBase 32768 32538669 widths1
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [checked1] at h
  simpa [widths1] using h.symm

def widths2 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked2 : geometricActiveStreamingTwinScan finiteTwinCheckedBase 32571437 widths2 = 151 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 32571437 32604205).card = 151 := by
  have h := geometricActiveStreamingTwinScan_spec finiteTwinCheckedBase 32768 32571437 widths2
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [checked2] at h
  simpa [widths2] using h.symm

def widths3 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked3 : geometricActiveStreamingTwinScan finiteTwinCheckedBase 32604205 widths3 = 168 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 32604205 32636973).card = 168 := by
  have h := geometricActiveStreamingTwinScan_spec finiteTwinCheckedBase 32768 32604205 widths3
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [checked3] at h
  simpa [widths3] using h.symm

theorem join_0_0 : (twinPrimeSegment 32505901 32571437).card = 253 := by
  simpa using combineTwinPrimeSegments (by decide : 32505901 ≤ 32538669)
    (by decide : 32538669 ≤ 32571437) block0 block1

theorem join_0_1 : (twinPrimeSegment 32571437 32636973).card = 319 := by
  simpa using combineTwinPrimeSegments (by decide : 32571437 ≤ 32604205)
    (by decide : 32604205 ≤ 32636973) block2 block3

theorem join_1_0 : (twinPrimeSegment 32505901 32636973).card = 572 := by
  simpa using combineTwinPrimeSegments (by decide : 32505901 ≤ 32571437)
    (by decide : 32571437 ≤ 32636973) join_0_0 join_0_1

theorem total : (twinPrimeSegment 32505901 32636973).card = 572 := join_1_0

end S015C08
end Sude.GeneratedTwinScan
