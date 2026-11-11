import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinGeometricScan

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S026C09
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def widths0 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked0 : geometricActiveStreamingTwinScan finiteTwinCheckedBase 55705645 widths0 = 138 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 55705645 55738413).card = 138 := by
  have h := geometricActiveStreamingTwinScan_spec finiteTwinCheckedBase 32768 55705645 widths0
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [checked0] at h
  simpa [widths0] using h.symm

def widths1 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked1 : geometricActiveStreamingTwinScan finiteTwinCheckedBase 55738413 widths1 = 147 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 55738413 55771181).card = 147 := by
  have h := geometricActiveStreamingTwinScan_spec finiteTwinCheckedBase 32768 55738413 widths1
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [checked1] at h
  simpa [widths1] using h.symm

def widths2 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked2 : geometricActiveStreamingTwinScan finiteTwinCheckedBase 55771181 widths2 = 143 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 55771181 55803949).card = 143 := by
  have h := geometricActiveStreamingTwinScan_spec finiteTwinCheckedBase 32768 55771181 widths2
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [checked2] at h
  simpa [widths2] using h.symm

def widths3 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked3 : geometricActiveStreamingTwinScan finiteTwinCheckedBase 55803949 widths3 = 124 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 55803949 55836717).card = 124 := by
  have h := geometricActiveStreamingTwinScan_spec finiteTwinCheckedBase 32768 55803949 widths3
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [checked3] at h
  simpa [widths3] using h.symm

theorem join_0_0 : (twinPrimeSegment 55705645 55771181).card = 285 := by
  simpa using combineTwinPrimeSegments (by decide : 55705645 ≤ 55738413)
    (by decide : 55738413 ≤ 55771181) block0 block1

theorem join_0_1 : (twinPrimeSegment 55771181 55836717).card = 267 := by
  simpa using combineTwinPrimeSegments (by decide : 55771181 ≤ 55803949)
    (by decide : 55803949 ≤ 55836717) block2 block3

theorem join_1_0 : (twinPrimeSegment 55705645 55836717).card = 552 := by
  simpa using combineTwinPrimeSegments (by decide : 55705645 ≤ 55771181)
    (by decide : 55771181 ≤ 55836717) join_0_0 join_0_1

theorem total : (twinPrimeSegment 55705645 55836717).card = 552 := join_1_0

end S026C09
end Sude.GeneratedTwinScan
