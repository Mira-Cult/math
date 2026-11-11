import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinGeometricScan

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S025C14
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def widths0 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked0 : geometricActiveStreamingTwinScan finiteTwinCheckedBase 54263853 widths0 = 121 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 54263853 54296621).card = 121 := by
  have h := geometricActiveStreamingTwinScan_spec finiteTwinCheckedBase 32768 54263853 widths0
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [checked0] at h
  simpa [widths0] using h.symm

def widths1 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked1 : geometricActiveStreamingTwinScan finiteTwinCheckedBase 54296621 widths1 = 140 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 54296621 54329389).card = 140 := by
  have h := geometricActiveStreamingTwinScan_spec finiteTwinCheckedBase 32768 54296621 widths1
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [checked1] at h
  simpa [widths1] using h.symm

def widths2 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked2 : geometricActiveStreamingTwinScan finiteTwinCheckedBase 54329389 widths2 = 138 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 54329389 54362157).card = 138 := by
  have h := geometricActiveStreamingTwinScan_spec finiteTwinCheckedBase 32768 54329389 widths2
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [checked2] at h
  simpa [widths2] using h.symm

def widths3 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked3 : geometricActiveStreamingTwinScan finiteTwinCheckedBase 54362157 widths3 = 114 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 54362157 54394925).card = 114 := by
  have h := geometricActiveStreamingTwinScan_spec finiteTwinCheckedBase 32768 54362157 widths3
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [checked3] at h
  simpa [widths3] using h.symm

theorem join_0_0 : (twinPrimeSegment 54263853 54329389).card = 261 := by
  simpa using combineTwinPrimeSegments (by decide : 54263853 ≤ 54296621)
    (by decide : 54296621 ≤ 54329389) block0 block1

theorem join_0_1 : (twinPrimeSegment 54329389 54394925).card = 252 := by
  simpa using combineTwinPrimeSegments (by decide : 54329389 ≤ 54362157)
    (by decide : 54362157 ≤ 54394925) block2 block3

theorem join_1_0 : (twinPrimeSegment 54263853 54394925).card = 513 := by
  simpa using combineTwinPrimeSegments (by decide : 54263853 ≤ 54329389)
    (by decide : 54329389 ≤ 54394925) join_0_0 join_0_1

theorem total : (twinPrimeSegment 54263853 54394925).card = 513 := join_1_0

end S025C14
end Sude.GeneratedTwinScan
