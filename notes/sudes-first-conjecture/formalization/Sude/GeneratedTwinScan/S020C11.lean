import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinGeometricScan

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S020C11
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def widths0 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked0 : geometricActiveStreamingTwinScan finiteTwinCheckedBase 43384877 widths0 = 137 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 43384877 43417645).card = 137 := by
  have h := geometricActiveStreamingTwinScan_spec finiteTwinCheckedBase 32768 43384877 widths0
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [checked0] at h
  simpa [widths0] using h.symm

def widths1 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked1 : geometricActiveStreamingTwinScan finiteTwinCheckedBase 43417645 widths1 = 145 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 43417645 43450413).card = 145 := by
  have h := geometricActiveStreamingTwinScan_spec finiteTwinCheckedBase 32768 43417645 widths1
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [checked1] at h
  simpa [widths1] using h.symm

def widths2 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked2 : geometricActiveStreamingTwinScan finiteTwinCheckedBase 43450413 widths2 = 128 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 43450413 43483181).card = 128 := by
  have h := geometricActiveStreamingTwinScan_spec finiteTwinCheckedBase 32768 43450413 widths2
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [checked2] at h
  simpa [widths2] using h.symm

def widths3 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked3 : geometricActiveStreamingTwinScan finiteTwinCheckedBase 43483181 widths3 = 139 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 43483181 43515949).card = 139 := by
  have h := geometricActiveStreamingTwinScan_spec finiteTwinCheckedBase 32768 43483181 widths3
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [checked3] at h
  simpa [widths3] using h.symm

theorem join_0_0 : (twinPrimeSegment 43384877 43450413).card = 282 := by
  simpa using combineTwinPrimeSegments (by decide : 43384877 ≤ 43417645)
    (by decide : 43417645 ≤ 43450413) block0 block1

theorem join_0_1 : (twinPrimeSegment 43450413 43515949).card = 267 := by
  simpa using combineTwinPrimeSegments (by decide : 43450413 ≤ 43483181)
    (by decide : 43483181 ≤ 43515949) block2 block3

theorem join_1_0 : (twinPrimeSegment 43384877 43515949).card = 549 := by
  simpa using combineTwinPrimeSegments (by decide : 43384877 ≤ 43450413)
    (by decide : 43450413 ≤ 43515949) join_0_0 join_0_1

theorem total : (twinPrimeSegment 43384877 43515949).card = 549 := join_1_0

end S020C11
end Sude.GeneratedTwinScan
