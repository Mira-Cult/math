import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinGeometricScan

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S020C06
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def widths0 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked0 : geometricActiveStreamingTwinScan finiteTwinCheckedBase 42729517 widths0 = 125 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 42729517 42762285).card = 125 := by
  have h := geometricActiveStreamingTwinScan_spec finiteTwinCheckedBase 32768 42729517 widths0
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [checked0] at h
  simpa [widths0] using h.symm

def widths1 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked1 : geometricActiveStreamingTwinScan finiteTwinCheckedBase 42762285 widths1 = 149 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 42762285 42795053).card = 149 := by
  have h := geometricActiveStreamingTwinScan_spec finiteTwinCheckedBase 32768 42762285 widths1
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [checked1] at h
  simpa [widths1] using h.symm

def widths2 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked2 : geometricActiveStreamingTwinScan finiteTwinCheckedBase 42795053 widths2 = 156 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 42795053 42827821).card = 156 := by
  have h := geometricActiveStreamingTwinScan_spec finiteTwinCheckedBase 32768 42795053 widths2
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [checked2] at h
  simpa [widths2] using h.symm

def widths3 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked3 : geometricActiveStreamingTwinScan finiteTwinCheckedBase 42827821 widths3 = 166 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 42827821 42860589).card = 166 := by
  have h := geometricActiveStreamingTwinScan_spec finiteTwinCheckedBase 32768 42827821 widths3
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [checked3] at h
  simpa [widths3] using h.symm

theorem join_0_0 : (twinPrimeSegment 42729517 42795053).card = 274 := by
  simpa using combineTwinPrimeSegments (by decide : 42729517 ≤ 42762285)
    (by decide : 42762285 ≤ 42795053) block0 block1

theorem join_0_1 : (twinPrimeSegment 42795053 42860589).card = 322 := by
  simpa using combineTwinPrimeSegments (by decide : 42795053 ≤ 42827821)
    (by decide : 42827821 ≤ 42860589) block2 block3

theorem join_1_0 : (twinPrimeSegment 42729517 42860589).card = 596 := by
  simpa using combineTwinPrimeSegments (by decide : 42729517 ≤ 42795053)
    (by decide : 42795053 ≤ 42860589) join_0_0 join_0_1

theorem total : (twinPrimeSegment 42729517 42860589).card = 596 := join_1_0

end S020C06
end Sude.GeneratedTwinScan
