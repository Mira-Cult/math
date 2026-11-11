import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinGeometricScan

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S021C06
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def widths0 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked0 : geometricActiveStreamingTwinScan finiteTwinCheckedBase 44826669 widths0 = 127 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 44826669 44859437).card = 127 := by
  have h := geometricActiveStreamingTwinScan_spec finiteTwinCheckedBase 32768 44826669 widths0
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [checked0] at h
  simpa [widths0] using h.symm

def widths1 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked1 : geometricActiveStreamingTwinScan finiteTwinCheckedBase 44859437 widths1 = 138 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 44859437 44892205).card = 138 := by
  have h := geometricActiveStreamingTwinScan_spec finiteTwinCheckedBase 32768 44859437 widths1
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [checked1] at h
  simpa [widths1] using h.symm

def widths2 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked2 : geometricActiveStreamingTwinScan finiteTwinCheckedBase 44892205 widths2 = 141 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 44892205 44924973).card = 141 := by
  have h := geometricActiveStreamingTwinScan_spec finiteTwinCheckedBase 32768 44892205 widths2
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [checked2] at h
  simpa [widths2] using h.symm

def widths3 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked3 : geometricActiveStreamingTwinScan finiteTwinCheckedBase 44924973 widths3 = 131 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 44924973 44957741).card = 131 := by
  have h := geometricActiveStreamingTwinScan_spec finiteTwinCheckedBase 32768 44924973 widths3
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [checked3] at h
  simpa [widths3] using h.symm

theorem join_0_0 : (twinPrimeSegment 44826669 44892205).card = 265 := by
  simpa using combineTwinPrimeSegments (by decide : 44826669 ≤ 44859437)
    (by decide : 44859437 ≤ 44892205) block0 block1

theorem join_0_1 : (twinPrimeSegment 44892205 44957741).card = 272 := by
  simpa using combineTwinPrimeSegments (by decide : 44892205 ≤ 44924973)
    (by decide : 44924973 ≤ 44957741) block2 block3

theorem join_1_0 : (twinPrimeSegment 44826669 44957741).card = 537 := by
  simpa using combineTwinPrimeSegments (by decide : 44826669 ≤ 44892205)
    (by decide : 44892205 ≤ 44957741) join_0_0 join_0_1

theorem total : (twinPrimeSegment 44826669 44957741).card = 537 := join_1_0

end S021C06
end Sude.GeneratedTwinScan
