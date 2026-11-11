import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinGeometricScan

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S027C09
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def widths0 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked0 : geometricActiveStreamingTwinScan finiteTwinCheckedBase 57802797 widths0 = 137 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 57802797 57835565).card = 137 := by
  have h := geometricActiveStreamingTwinScan_spec finiteTwinCheckedBase 32768 57802797 widths0
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [checked0] at h
  simpa [widths0] using h.symm

def widths1 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked1 : geometricActiveStreamingTwinScan finiteTwinCheckedBase 57835565 widths1 = 141 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 57835565 57868333).card = 141 := by
  have h := geometricActiveStreamingTwinScan_spec finiteTwinCheckedBase 32768 57835565 widths1
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [checked1] at h
  simpa [widths1] using h.symm

def widths2 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked2 : geometricActiveStreamingTwinScan finiteTwinCheckedBase 57868333 widths2 = 125 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 57868333 57901101).card = 125 := by
  have h := geometricActiveStreamingTwinScan_spec finiteTwinCheckedBase 32768 57868333 widths2
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [checked2] at h
  simpa [widths2] using h.symm

def widths3 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked3 : geometricActiveStreamingTwinScan finiteTwinCheckedBase 57901101 widths3 = 133 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 57901101 57933869).card = 133 := by
  have h := geometricActiveStreamingTwinScan_spec finiteTwinCheckedBase 32768 57901101 widths3
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [checked3] at h
  simpa [widths3] using h.symm

theorem join_0_0 : (twinPrimeSegment 57802797 57868333).card = 278 := by
  simpa using combineTwinPrimeSegments (by decide : 57802797 ≤ 57835565)
    (by decide : 57835565 ≤ 57868333) block0 block1

theorem join_0_1 : (twinPrimeSegment 57868333 57933869).card = 258 := by
  simpa using combineTwinPrimeSegments (by decide : 57868333 ≤ 57901101)
    (by decide : 57901101 ≤ 57933869) block2 block3

theorem join_1_0 : (twinPrimeSegment 57802797 57933869).card = 536 := by
  simpa using combineTwinPrimeSegments (by decide : 57802797 ≤ 57868333)
    (by decide : 57868333 ≤ 57933869) join_0_0 join_0_1

theorem total : (twinPrimeSegment 57802797 57933869).card = 536 := join_1_0

end S027C09
end Sude.GeneratedTwinScan
