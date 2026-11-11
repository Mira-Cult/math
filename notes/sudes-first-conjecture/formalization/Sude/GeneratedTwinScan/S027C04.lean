import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinGeometricScan

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S027C04
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def widths0 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked0 : geometricActiveStreamingTwinScan finiteTwinCheckedBase 57147437 widths0 = 150 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 57147437 57180205).card = 150 := by
  have h := geometricActiveStreamingTwinScan_spec finiteTwinCheckedBase 32768 57147437 widths0
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [checked0] at h
  simpa [widths0] using h.symm

def widths1 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked1 : geometricActiveStreamingTwinScan finiteTwinCheckedBase 57180205 widths1 = 136 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 57180205 57212973).card = 136 := by
  have h := geometricActiveStreamingTwinScan_spec finiteTwinCheckedBase 32768 57180205 widths1
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [checked1] at h
  simpa [widths1] using h.symm

def widths2 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked2 : geometricActiveStreamingTwinScan finiteTwinCheckedBase 57212973 widths2 = 139 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 57212973 57245741).card = 139 := by
  have h := geometricActiveStreamingTwinScan_spec finiteTwinCheckedBase 32768 57212973 widths2
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [checked2] at h
  simpa [widths2] using h.symm

def widths3 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked3 : geometricActiveStreamingTwinScan finiteTwinCheckedBase 57245741 widths3 = 152 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 57245741 57278509).card = 152 := by
  have h := geometricActiveStreamingTwinScan_spec finiteTwinCheckedBase 32768 57245741 widths3
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [checked3] at h
  simpa [widths3] using h.symm

theorem join_0_0 : (twinPrimeSegment 57147437 57212973).card = 286 := by
  simpa using combineTwinPrimeSegments (by decide : 57147437 ≤ 57180205)
    (by decide : 57180205 ≤ 57212973) block0 block1

theorem join_0_1 : (twinPrimeSegment 57212973 57278509).card = 291 := by
  simpa using combineTwinPrimeSegments (by decide : 57212973 ≤ 57245741)
    (by decide : 57245741 ≤ 57278509) block2 block3

theorem join_1_0 : (twinPrimeSegment 57147437 57278509).card = 577 := by
  simpa using combineTwinPrimeSegments (by decide : 57147437 ≤ 57212973)
    (by decide : 57212973 ≤ 57278509) join_0_0 join_0_1

theorem total : (twinPrimeSegment 57147437 57278509).card = 577 := join_1_0

end S027C04
end Sude.GeneratedTwinScan
