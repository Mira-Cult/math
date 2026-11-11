import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinGeometricScan

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S024C15
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def widths0 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked0 : geometricActiveStreamingTwinScan finiteTwinCheckedBase 52297773 widths0 = 132 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 52297773 52330541).card = 132 := by
  have h := geometricActiveStreamingTwinScan_spec finiteTwinCheckedBase 32768 52297773 widths0
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [checked0] at h
  simpa [widths0] using h.symm

def widths1 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked1 : geometricActiveStreamingTwinScan finiteTwinCheckedBase 52330541 widths1 = 148 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 52330541 52363309).card = 148 := by
  have h := geometricActiveStreamingTwinScan_spec finiteTwinCheckedBase 32768 52330541 widths1
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [checked1] at h
  simpa [widths1] using h.symm

def widths2 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked2 : geometricActiveStreamingTwinScan finiteTwinCheckedBase 52363309 widths2 = 124 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 52363309 52396077).card = 124 := by
  have h := geometricActiveStreamingTwinScan_spec finiteTwinCheckedBase 32768 52363309 widths2
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [checked2] at h
  simpa [widths2] using h.symm

def widths3 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked3 : geometricActiveStreamingTwinScan finiteTwinCheckedBase 52396077 widths3 = 138 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 52396077 52428845).card = 138 := by
  have h := geometricActiveStreamingTwinScan_spec finiteTwinCheckedBase 32768 52396077 widths3
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [checked3] at h
  simpa [widths3] using h.symm

theorem join_0_0 : (twinPrimeSegment 52297773 52363309).card = 280 := by
  simpa using combineTwinPrimeSegments (by decide : 52297773 ≤ 52330541)
    (by decide : 52330541 ≤ 52363309) block0 block1

theorem join_0_1 : (twinPrimeSegment 52363309 52428845).card = 262 := by
  simpa using combineTwinPrimeSegments (by decide : 52363309 ≤ 52396077)
    (by decide : 52396077 ≤ 52428845) block2 block3

theorem join_1_0 : (twinPrimeSegment 52297773 52428845).card = 542 := by
  simpa using combineTwinPrimeSegments (by decide : 52297773 ≤ 52363309)
    (by decide : 52363309 ≤ 52428845) join_0_0 join_0_1

theorem total : (twinPrimeSegment 52297773 52428845).card = 542 := join_1_0

end S024C15
end Sude.GeneratedTwinScan
