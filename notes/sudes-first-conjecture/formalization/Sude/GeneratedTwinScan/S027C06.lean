import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinGeometricScan

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S027C06
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def widths0 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked0 : geometricActiveStreamingTwinScan finiteTwinCheckedBase 57409581 widths0 = 146 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 57409581 57442349).card = 146 := by
  have h := geometricActiveStreamingTwinScan_spec finiteTwinCheckedBase 32768 57409581 widths0
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [checked0] at h
  simpa [widths0] using h.symm

def widths1 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked1 : geometricActiveStreamingTwinScan finiteTwinCheckedBase 57442349 widths1 = 138 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 57442349 57475117).card = 138 := by
  have h := geometricActiveStreamingTwinScan_spec finiteTwinCheckedBase 32768 57442349 widths1
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [checked1] at h
  simpa [widths1] using h.symm

def widths2 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked2 : geometricActiveStreamingTwinScan finiteTwinCheckedBase 57475117 widths2 = 140 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 57475117 57507885).card = 140 := by
  have h := geometricActiveStreamingTwinScan_spec finiteTwinCheckedBase 32768 57475117 widths2
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [checked2] at h
  simpa [widths2] using h.symm

def widths3 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked3 : geometricActiveStreamingTwinScan finiteTwinCheckedBase 57507885 widths3 = 137 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 57507885 57540653).card = 137 := by
  have h := geometricActiveStreamingTwinScan_spec finiteTwinCheckedBase 32768 57507885 widths3
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [checked3] at h
  simpa [widths3] using h.symm

theorem join_0_0 : (twinPrimeSegment 57409581 57475117).card = 284 := by
  simpa using combineTwinPrimeSegments (by decide : 57409581 ≤ 57442349)
    (by decide : 57442349 ≤ 57475117) block0 block1

theorem join_0_1 : (twinPrimeSegment 57475117 57540653).card = 277 := by
  simpa using combineTwinPrimeSegments (by decide : 57475117 ≤ 57507885)
    (by decide : 57507885 ≤ 57540653) block2 block3

theorem join_1_0 : (twinPrimeSegment 57409581 57540653).card = 561 := by
  simpa using combineTwinPrimeSegments (by decide : 57409581 ≤ 57475117)
    (by decide : 57475117 ≤ 57540653) join_0_0 join_0_1

theorem total : (twinPrimeSegment 57409581 57540653).card = 561 := join_1_0

end S027C06
end Sude.GeneratedTwinScan
