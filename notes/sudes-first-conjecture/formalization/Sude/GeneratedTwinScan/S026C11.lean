import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinGeometricScan

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S026C11
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def widths0 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked0 : geometricActiveStreamingTwinScan finiteTwinCheckedBase 55967789 widths0 = 136 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 55967789 56000557).card = 136 := by
  have h := geometricActiveStreamingTwinScan_spec finiteTwinCheckedBase 32768 55967789 widths0
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [checked0] at h
  simpa [widths0] using h.symm

def widths1 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked1 : geometricActiveStreamingTwinScan finiteTwinCheckedBase 56000557 widths1 = 122 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 56000557 56033325).card = 122 := by
  have h := geometricActiveStreamingTwinScan_spec finiteTwinCheckedBase 32768 56000557 widths1
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [checked1] at h
  simpa [widths1] using h.symm

def widths2 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked2 : geometricActiveStreamingTwinScan finiteTwinCheckedBase 56033325 widths2 = 150 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 56033325 56066093).card = 150 := by
  have h := geometricActiveStreamingTwinScan_spec finiteTwinCheckedBase 32768 56033325 widths2
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [checked2] at h
  simpa [widths2] using h.symm

def widths3 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked3 : geometricActiveStreamingTwinScan finiteTwinCheckedBase 56066093 widths3 = 138 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 56066093 56098861).card = 138 := by
  have h := geometricActiveStreamingTwinScan_spec finiteTwinCheckedBase 32768 56066093 widths3
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [checked3] at h
  simpa [widths3] using h.symm

theorem join_0_0 : (twinPrimeSegment 55967789 56033325).card = 258 := by
  simpa using combineTwinPrimeSegments (by decide : 55967789 ≤ 56000557)
    (by decide : 56000557 ≤ 56033325) block0 block1

theorem join_0_1 : (twinPrimeSegment 56033325 56098861).card = 288 := by
  simpa using combineTwinPrimeSegments (by decide : 56033325 ≤ 56066093)
    (by decide : 56066093 ≤ 56098861) block2 block3

theorem join_1_0 : (twinPrimeSegment 55967789 56098861).card = 546 := by
  simpa using combineTwinPrimeSegments (by decide : 55967789 ≤ 56033325)
    (by decide : 56033325 ≤ 56098861) join_0_0 join_0_1

theorem total : (twinPrimeSegment 55967789 56098861).card = 546 := join_1_0

end S026C11
end Sude.GeneratedTwinScan
