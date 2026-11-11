import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinGeometricScan

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S022C07
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def widths0 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked0 : geometricActiveStreamingTwinScan finiteTwinCheckedBase 47054893 widths0 = 120 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 47054893 47087661).card = 120 := by
  have h := geometricActiveStreamingTwinScan_spec finiteTwinCheckedBase 32768 47054893 widths0
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [checked0] at h
  simpa [widths0] using h.symm

def widths1 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked1 : geometricActiveStreamingTwinScan finiteTwinCheckedBase 47087661 widths1 = 133 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 47087661 47120429).card = 133 := by
  have h := geometricActiveStreamingTwinScan_spec finiteTwinCheckedBase 32768 47087661 widths1
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [checked1] at h
  simpa [widths1] using h.symm

def widths2 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked2 : geometricActiveStreamingTwinScan finiteTwinCheckedBase 47120429 widths2 = 149 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 47120429 47153197).card = 149 := by
  have h := geometricActiveStreamingTwinScan_spec finiteTwinCheckedBase 32768 47120429 widths2
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [checked2] at h
  simpa [widths2] using h.symm

def widths3 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked3 : geometricActiveStreamingTwinScan finiteTwinCheckedBase 47153197 widths3 = 141 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 47153197 47185965).card = 141 := by
  have h := geometricActiveStreamingTwinScan_spec finiteTwinCheckedBase 32768 47153197 widths3
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [checked3] at h
  simpa [widths3] using h.symm

theorem join_0_0 : (twinPrimeSegment 47054893 47120429).card = 253 := by
  simpa using combineTwinPrimeSegments (by decide : 47054893 ≤ 47087661)
    (by decide : 47087661 ≤ 47120429) block0 block1

theorem join_0_1 : (twinPrimeSegment 47120429 47185965).card = 290 := by
  simpa using combineTwinPrimeSegments (by decide : 47120429 ≤ 47153197)
    (by decide : 47153197 ≤ 47185965) block2 block3

theorem join_1_0 : (twinPrimeSegment 47054893 47185965).card = 543 := by
  simpa using combineTwinPrimeSegments (by decide : 47054893 ≤ 47120429)
    (by decide : 47120429 ≤ 47185965) join_0_0 join_0_1

theorem total : (twinPrimeSegment 47054893 47185965).card = 543 := join_1_0

end S022C07
end Sude.GeneratedTwinScan
