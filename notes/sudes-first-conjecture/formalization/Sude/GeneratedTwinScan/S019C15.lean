import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinGeometricScan

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S019C15
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def widths0 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked0 : geometricActiveStreamingTwinScan finiteTwinCheckedBase 41812013 widths0 = 145 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 41812013 41844781).card = 145 := by
  have h := geometricActiveStreamingTwinScan_spec finiteTwinCheckedBase 32768 41812013 widths0
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [checked0] at h
  simpa [widths0] using h.symm

def widths1 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked1 : geometricActiveStreamingTwinScan finiteTwinCheckedBase 41844781 widths1 = 138 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 41844781 41877549).card = 138 := by
  have h := geometricActiveStreamingTwinScan_spec finiteTwinCheckedBase 32768 41844781 widths1
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [checked1] at h
  simpa [widths1] using h.symm

def widths2 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked2 : geometricActiveStreamingTwinScan finiteTwinCheckedBase 41877549 widths2 = 133 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 41877549 41910317).card = 133 := by
  have h := geometricActiveStreamingTwinScan_spec finiteTwinCheckedBase 32768 41877549 widths2
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [checked2] at h
  simpa [widths2] using h.symm

def widths3 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked3 : geometricActiveStreamingTwinScan finiteTwinCheckedBase 41910317 widths3 = 126 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 41910317 41943085).card = 126 := by
  have h := geometricActiveStreamingTwinScan_spec finiteTwinCheckedBase 32768 41910317 widths3
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [checked3] at h
  simpa [widths3] using h.symm

theorem join_0_0 : (twinPrimeSegment 41812013 41877549).card = 283 := by
  simpa using combineTwinPrimeSegments (by decide : 41812013 ≤ 41844781)
    (by decide : 41844781 ≤ 41877549) block0 block1

theorem join_0_1 : (twinPrimeSegment 41877549 41943085).card = 259 := by
  simpa using combineTwinPrimeSegments (by decide : 41877549 ≤ 41910317)
    (by decide : 41910317 ≤ 41943085) block2 block3

theorem join_1_0 : (twinPrimeSegment 41812013 41943085).card = 542 := by
  simpa using combineTwinPrimeSegments (by decide : 41812013 ≤ 41877549)
    (by decide : 41877549 ≤ 41943085) join_0_0 join_0_1

theorem total : (twinPrimeSegment 41812013 41943085).card = 542 := join_1_0

end S019C15
end Sude.GeneratedTwinScan
