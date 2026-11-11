import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinGeometricScan

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S024C00
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def widths0 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked0 : geometricActiveStreamingTwinScan finiteTwinCheckedBase 50331693 widths0 = 143 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 50331693 50364461).card = 143 := by
  have h := geometricActiveStreamingTwinScan_spec finiteTwinCheckedBase 32768 50331693 widths0
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [checked0] at h
  simpa [widths0] using h.symm

def widths1 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked1 : geometricActiveStreamingTwinScan finiteTwinCheckedBase 50364461 widths1 = 132 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 50364461 50397229).card = 132 := by
  have h := geometricActiveStreamingTwinScan_spec finiteTwinCheckedBase 32768 50364461 widths1
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [checked1] at h
  simpa [widths1] using h.symm

def widths2 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked2 : geometricActiveStreamingTwinScan finiteTwinCheckedBase 50397229 widths2 = 131 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 50397229 50429997).card = 131 := by
  have h := geometricActiveStreamingTwinScan_spec finiteTwinCheckedBase 32768 50397229 widths2
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [checked2] at h
  simpa [widths2] using h.symm

def widths3 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked3 : geometricActiveStreamingTwinScan finiteTwinCheckedBase 50429997 widths3 = 137 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 50429997 50462765).card = 137 := by
  have h := geometricActiveStreamingTwinScan_spec finiteTwinCheckedBase 32768 50429997 widths3
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [checked3] at h
  simpa [widths3] using h.symm

theorem join_0_0 : (twinPrimeSegment 50331693 50397229).card = 275 := by
  simpa using combineTwinPrimeSegments (by decide : 50331693 ≤ 50364461)
    (by decide : 50364461 ≤ 50397229) block0 block1

theorem join_0_1 : (twinPrimeSegment 50397229 50462765).card = 268 := by
  simpa using combineTwinPrimeSegments (by decide : 50397229 ≤ 50429997)
    (by decide : 50429997 ≤ 50462765) block2 block3

theorem join_1_0 : (twinPrimeSegment 50331693 50462765).card = 543 := by
  simpa using combineTwinPrimeSegments (by decide : 50331693 ≤ 50397229)
    (by decide : 50397229 ≤ 50462765) join_0_0 join_0_1

theorem total : (twinPrimeSegment 50331693 50462765).card = 543 := join_1_0

end S024C00
end Sude.GeneratedTwinScan
