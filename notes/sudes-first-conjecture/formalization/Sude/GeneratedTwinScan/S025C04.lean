import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinGeometricScan

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S025C04
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def widths0 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked0 : geometricActiveStreamingTwinScan finiteTwinCheckedBase 52953133 widths0 = 148 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 52953133 52985901).card = 148 := by
  have h := geometricActiveStreamingTwinScan_spec finiteTwinCheckedBase 32768 52953133 widths0
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [checked0] at h
  simpa [widths0] using h.symm

def widths1 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked1 : geometricActiveStreamingTwinScan finiteTwinCheckedBase 52985901 widths1 = 139 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 52985901 53018669).card = 139 := by
  have h := geometricActiveStreamingTwinScan_spec finiteTwinCheckedBase 32768 52985901 widths1
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [checked1] at h
  simpa [widths1] using h.symm

def widths2 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked2 : geometricActiveStreamingTwinScan finiteTwinCheckedBase 53018669 widths2 = 140 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 53018669 53051437).card = 140 := by
  have h := geometricActiveStreamingTwinScan_spec finiteTwinCheckedBase 32768 53018669 widths2
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [checked2] at h
  simpa [widths2] using h.symm

def widths3 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked3 : geometricActiveStreamingTwinScan finiteTwinCheckedBase 53051437 widths3 = 142 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 53051437 53084205).card = 142 := by
  have h := geometricActiveStreamingTwinScan_spec finiteTwinCheckedBase 32768 53051437 widths3
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [checked3] at h
  simpa [widths3] using h.symm

theorem join_0_0 : (twinPrimeSegment 52953133 53018669).card = 287 := by
  simpa using combineTwinPrimeSegments (by decide : 52953133 ≤ 52985901)
    (by decide : 52985901 ≤ 53018669) block0 block1

theorem join_0_1 : (twinPrimeSegment 53018669 53084205).card = 282 := by
  simpa using combineTwinPrimeSegments (by decide : 53018669 ≤ 53051437)
    (by decide : 53051437 ≤ 53084205) block2 block3

theorem join_1_0 : (twinPrimeSegment 52953133 53084205).card = 569 := by
  simpa using combineTwinPrimeSegments (by decide : 52953133 ≤ 53018669)
    (by decide : 53018669 ≤ 53084205) join_0_0 join_0_1

theorem total : (twinPrimeSegment 52953133 53084205).card = 569 := join_1_0

end S025C04
end Sude.GeneratedTwinScan
