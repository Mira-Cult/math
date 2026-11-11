import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinGeometricScan

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S017C01
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def widths0 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked0 : geometricActiveStreamingTwinScan finiteTwinCheckedBase 35782701 widths0 = 130 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 35782701 35815469).card = 130 := by
  have h := geometricActiveStreamingTwinScan_spec finiteTwinCheckedBase 32768 35782701 widths0
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [checked0] at h
  simpa [widths0] using h.symm

def widths1 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked1 : geometricActiveStreamingTwinScan finiteTwinCheckedBase 35815469 widths1 = 148 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 35815469 35848237).card = 148 := by
  have h := geometricActiveStreamingTwinScan_spec finiteTwinCheckedBase 32768 35815469 widths1
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [checked1] at h
  simpa [widths1] using h.symm

def widths2 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked2 : geometricActiveStreamingTwinScan finiteTwinCheckedBase 35848237 widths2 = 137 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 35848237 35881005).card = 137 := by
  have h := geometricActiveStreamingTwinScan_spec finiteTwinCheckedBase 32768 35848237 widths2
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [checked2] at h
  simpa [widths2] using h.symm

def widths3 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked3 : geometricActiveStreamingTwinScan finiteTwinCheckedBase 35881005 widths3 = 145 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 35881005 35913773).card = 145 := by
  have h := geometricActiveStreamingTwinScan_spec finiteTwinCheckedBase 32768 35881005 widths3
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [checked3] at h
  simpa [widths3] using h.symm

theorem join_0_0 : (twinPrimeSegment 35782701 35848237).card = 278 := by
  simpa using combineTwinPrimeSegments (by decide : 35782701 ≤ 35815469)
    (by decide : 35815469 ≤ 35848237) block0 block1

theorem join_0_1 : (twinPrimeSegment 35848237 35913773).card = 282 := by
  simpa using combineTwinPrimeSegments (by decide : 35848237 ≤ 35881005)
    (by decide : 35881005 ≤ 35913773) block2 block3

theorem join_1_0 : (twinPrimeSegment 35782701 35913773).card = 560 := by
  simpa using combineTwinPrimeSegments (by decide : 35782701 ≤ 35848237)
    (by decide : 35848237 ≤ 35913773) join_0_0 join_0_1

theorem total : (twinPrimeSegment 35782701 35913773).card = 560 := join_1_0

end S017C01
end Sude.GeneratedTwinScan
