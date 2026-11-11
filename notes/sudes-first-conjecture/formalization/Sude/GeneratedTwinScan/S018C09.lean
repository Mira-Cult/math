import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinGeometricScan

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S018C09
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def widths0 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked0 : geometricActiveStreamingTwinScan finiteTwinCheckedBase 38928429 widths0 = 159 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 38928429 38961197).card = 159 := by
  have h := geometricActiveStreamingTwinScan_spec finiteTwinCheckedBase 32768 38928429 widths0
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [checked0] at h
  simpa [widths0] using h.symm

def widths1 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked1 : geometricActiveStreamingTwinScan finiteTwinCheckedBase 38961197 widths1 = 134 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 38961197 38993965).card = 134 := by
  have h := geometricActiveStreamingTwinScan_spec finiteTwinCheckedBase 32768 38961197 widths1
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [checked1] at h
  simpa [widths1] using h.symm

def widths2 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked2 : geometricActiveStreamingTwinScan finiteTwinCheckedBase 38993965 widths2 = 127 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 38993965 39026733).card = 127 := by
  have h := geometricActiveStreamingTwinScan_spec finiteTwinCheckedBase 32768 38993965 widths2
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [checked2] at h
  simpa [widths2] using h.symm

def widths3 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked3 : geometricActiveStreamingTwinScan finiteTwinCheckedBase 39026733 widths3 = 125 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 39026733 39059501).card = 125 := by
  have h := geometricActiveStreamingTwinScan_spec finiteTwinCheckedBase 32768 39026733 widths3
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [checked3] at h
  simpa [widths3] using h.symm

theorem join_0_0 : (twinPrimeSegment 38928429 38993965).card = 293 := by
  simpa using combineTwinPrimeSegments (by decide : 38928429 ≤ 38961197)
    (by decide : 38961197 ≤ 38993965) block0 block1

theorem join_0_1 : (twinPrimeSegment 38993965 39059501).card = 252 := by
  simpa using combineTwinPrimeSegments (by decide : 38993965 ≤ 39026733)
    (by decide : 39026733 ≤ 39059501) block2 block3

theorem join_1_0 : (twinPrimeSegment 38928429 39059501).card = 545 := by
  simpa using combineTwinPrimeSegments (by decide : 38928429 ≤ 38993965)
    (by decide : 38993965 ≤ 39059501) join_0_0 join_0_1

theorem total : (twinPrimeSegment 38928429 39059501).card = 545 := join_1_0

end S018C09
end Sude.GeneratedTwinScan
