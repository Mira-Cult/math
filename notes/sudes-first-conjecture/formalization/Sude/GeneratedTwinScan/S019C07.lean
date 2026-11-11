import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinGeometricScan

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S019C07
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def widths0 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked0 : geometricActiveStreamingTwinScan finiteTwinCheckedBase 40763437 widths0 = 157 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 40763437 40796205).card = 157 := by
  have h := geometricActiveStreamingTwinScan_spec finiteTwinCheckedBase 32768 40763437 widths0
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [checked0] at h
  simpa [widths0] using h.symm

def widths1 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked1 : geometricActiveStreamingTwinScan finiteTwinCheckedBase 40796205 widths1 = 141 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 40796205 40828973).card = 141 := by
  have h := geometricActiveStreamingTwinScan_spec finiteTwinCheckedBase 32768 40796205 widths1
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [checked1] at h
  simpa [widths1] using h.symm

def widths2 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked2 : geometricActiveStreamingTwinScan finiteTwinCheckedBase 40828973 widths2 = 159 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 40828973 40861741).card = 159 := by
  have h := geometricActiveStreamingTwinScan_spec finiteTwinCheckedBase 32768 40828973 widths2
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [checked2] at h
  simpa [widths2] using h.symm

def widths3 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked3 : geometricActiveStreamingTwinScan finiteTwinCheckedBase 40861741 widths3 = 146 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 40861741 40894509).card = 146 := by
  have h := geometricActiveStreamingTwinScan_spec finiteTwinCheckedBase 32768 40861741 widths3
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [checked3] at h
  simpa [widths3] using h.symm

theorem join_0_0 : (twinPrimeSegment 40763437 40828973).card = 298 := by
  simpa using combineTwinPrimeSegments (by decide : 40763437 ≤ 40796205)
    (by decide : 40796205 ≤ 40828973) block0 block1

theorem join_0_1 : (twinPrimeSegment 40828973 40894509).card = 305 := by
  simpa using combineTwinPrimeSegments (by decide : 40828973 ≤ 40861741)
    (by decide : 40861741 ≤ 40894509) block2 block3

theorem join_1_0 : (twinPrimeSegment 40763437 40894509).card = 603 := by
  simpa using combineTwinPrimeSegments (by decide : 40763437 ≤ 40828973)
    (by decide : 40828973 ≤ 40894509) join_0_0 join_0_1

theorem total : (twinPrimeSegment 40763437 40894509).card = 603 := join_1_0

end S019C07
end Sude.GeneratedTwinScan
