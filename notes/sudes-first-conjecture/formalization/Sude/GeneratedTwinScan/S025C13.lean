import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinGeometricScan

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S025C13
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def widths0 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked0 : geometricActiveStreamingTwinScan finiteTwinCheckedBase 54132781 widths0 = 141 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 54132781 54165549).card = 141 := by
  have h := geometricActiveStreamingTwinScan_spec finiteTwinCheckedBase 32768 54132781 widths0
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [checked0] at h
  simpa [widths0] using h.symm

def widths1 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked1 : geometricActiveStreamingTwinScan finiteTwinCheckedBase 54165549 widths1 = 128 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 54165549 54198317).card = 128 := by
  have h := geometricActiveStreamingTwinScan_spec finiteTwinCheckedBase 32768 54165549 widths1
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [checked1] at h
  simpa [widths1] using h.symm

def widths2 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked2 : geometricActiveStreamingTwinScan finiteTwinCheckedBase 54198317 widths2 = 140 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 54198317 54231085).card = 140 := by
  have h := geometricActiveStreamingTwinScan_spec finiteTwinCheckedBase 32768 54198317 widths2
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [checked2] at h
  simpa [widths2] using h.symm

def widths3 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked3 : geometricActiveStreamingTwinScan finiteTwinCheckedBase 54231085 widths3 = 157 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 54231085 54263853).card = 157 := by
  have h := geometricActiveStreamingTwinScan_spec finiteTwinCheckedBase 32768 54231085 widths3
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [checked3] at h
  simpa [widths3] using h.symm

theorem join_0_0 : (twinPrimeSegment 54132781 54198317).card = 269 := by
  simpa using combineTwinPrimeSegments (by decide : 54132781 ≤ 54165549)
    (by decide : 54165549 ≤ 54198317) block0 block1

theorem join_0_1 : (twinPrimeSegment 54198317 54263853).card = 297 := by
  simpa using combineTwinPrimeSegments (by decide : 54198317 ≤ 54231085)
    (by decide : 54231085 ≤ 54263853) block2 block3

theorem join_1_0 : (twinPrimeSegment 54132781 54263853).card = 566 := by
  simpa using combineTwinPrimeSegments (by decide : 54132781 ≤ 54198317)
    (by decide : 54198317 ≤ 54263853) join_0_0 join_0_1

theorem total : (twinPrimeSegment 54132781 54263853).card = 566 := join_1_0

end S025C13
end Sude.GeneratedTwinScan
