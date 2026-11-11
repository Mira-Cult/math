import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinGeometricScan

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S025C15
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def widths0 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked0 : geometricActiveStreamingTwinScan finiteTwinCheckedBase 54394925 widths0 = 135 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 54394925 54427693).card = 135 := by
  have h := geometricActiveStreamingTwinScan_spec finiteTwinCheckedBase 32768 54394925 widths0
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [checked0] at h
  simpa [widths0] using h.symm

def widths1 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked1 : geometricActiveStreamingTwinScan finiteTwinCheckedBase 54427693 widths1 = 135 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 54427693 54460461).card = 135 := by
  have h := geometricActiveStreamingTwinScan_spec finiteTwinCheckedBase 32768 54427693 widths1
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [checked1] at h
  simpa [widths1] using h.symm

def widths2 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked2 : geometricActiveStreamingTwinScan finiteTwinCheckedBase 54460461 widths2 = 117 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 54460461 54493229).card = 117 := by
  have h := geometricActiveStreamingTwinScan_spec finiteTwinCheckedBase 32768 54460461 widths2
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [checked2] at h
  simpa [widths2] using h.symm

def widths3 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked3 : geometricActiveStreamingTwinScan finiteTwinCheckedBase 54493229 widths3 = 142 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 54493229 54525997).card = 142 := by
  have h := geometricActiveStreamingTwinScan_spec finiteTwinCheckedBase 32768 54493229 widths3
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [checked3] at h
  simpa [widths3] using h.symm

theorem join_0_0 : (twinPrimeSegment 54394925 54460461).card = 270 := by
  simpa using combineTwinPrimeSegments (by decide : 54394925 ≤ 54427693)
    (by decide : 54427693 ≤ 54460461) block0 block1

theorem join_0_1 : (twinPrimeSegment 54460461 54525997).card = 259 := by
  simpa using combineTwinPrimeSegments (by decide : 54460461 ≤ 54493229)
    (by decide : 54493229 ≤ 54525997) block2 block3

theorem join_1_0 : (twinPrimeSegment 54394925 54525997).card = 529 := by
  simpa using combineTwinPrimeSegments (by decide : 54394925 ≤ 54460461)
    (by decide : 54460461 ≤ 54525997) join_0_0 join_0_1

theorem total : (twinPrimeSegment 54394925 54525997).card = 529 := join_1_0

end S025C15
end Sude.GeneratedTwinScan
