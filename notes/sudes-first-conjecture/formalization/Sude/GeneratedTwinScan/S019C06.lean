import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinGeometricScan

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S019C06
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def widths0 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked0 : geometricActiveStreamingTwinScan finiteTwinCheckedBase 40632365 widths0 = 162 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 40632365 40665133).card = 162 := by
  have h := geometricActiveStreamingTwinScan_spec finiteTwinCheckedBase 32768 40632365 widths0
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [checked0] at h
  simpa [widths0] using h.symm

def widths1 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked1 : geometricActiveStreamingTwinScan finiteTwinCheckedBase 40665133 widths1 = 149 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 40665133 40697901).card = 149 := by
  have h := geometricActiveStreamingTwinScan_spec finiteTwinCheckedBase 32768 40665133 widths1
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [checked1] at h
  simpa [widths1] using h.symm

def widths2 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked2 : geometricActiveStreamingTwinScan finiteTwinCheckedBase 40697901 widths2 = 128 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 40697901 40730669).card = 128 := by
  have h := geometricActiveStreamingTwinScan_spec finiteTwinCheckedBase 32768 40697901 widths2
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [checked2] at h
  simpa [widths2] using h.symm

def widths3 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked3 : geometricActiveStreamingTwinScan finiteTwinCheckedBase 40730669 widths3 = 129 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 40730669 40763437).card = 129 := by
  have h := geometricActiveStreamingTwinScan_spec finiteTwinCheckedBase 32768 40730669 widths3
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [checked3] at h
  simpa [widths3] using h.symm

theorem join_0_0 : (twinPrimeSegment 40632365 40697901).card = 311 := by
  simpa using combineTwinPrimeSegments (by decide : 40632365 ≤ 40665133)
    (by decide : 40665133 ≤ 40697901) block0 block1

theorem join_0_1 : (twinPrimeSegment 40697901 40763437).card = 257 := by
  simpa using combineTwinPrimeSegments (by decide : 40697901 ≤ 40730669)
    (by decide : 40730669 ≤ 40763437) block2 block3

theorem join_1_0 : (twinPrimeSegment 40632365 40763437).card = 568 := by
  simpa using combineTwinPrimeSegments (by decide : 40632365 ≤ 40697901)
    (by decide : 40697901 ≤ 40763437) join_0_0 join_0_1

theorem total : (twinPrimeSegment 40632365 40763437).card = 568 := join_1_0

end S019C06
end Sude.GeneratedTwinScan
