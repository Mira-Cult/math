import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinGeometricScan

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S025C10
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def widths0 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked0 : geometricActiveStreamingTwinScan finiteTwinCheckedBase 53739565 widths0 = 132 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 53739565 53772333).card = 132 := by
  have h := geometricActiveStreamingTwinScan_spec finiteTwinCheckedBase 32768 53739565 widths0
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [checked0] at h
  simpa [widths0] using h.symm

def widths1 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked1 : geometricActiveStreamingTwinScan finiteTwinCheckedBase 53772333 widths1 = 132 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 53772333 53805101).card = 132 := by
  have h := geometricActiveStreamingTwinScan_spec finiteTwinCheckedBase 32768 53772333 widths1
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [checked1] at h
  simpa [widths1] using h.symm

def widths2 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked2 : geometricActiveStreamingTwinScan finiteTwinCheckedBase 53805101 widths2 = 139 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 53805101 53837869).card = 139 := by
  have h := geometricActiveStreamingTwinScan_spec finiteTwinCheckedBase 32768 53805101 widths2
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [checked2] at h
  simpa [widths2] using h.symm

def widths3 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked3 : geometricActiveStreamingTwinScan finiteTwinCheckedBase 53837869 widths3 = 131 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 53837869 53870637).card = 131 := by
  have h := geometricActiveStreamingTwinScan_spec finiteTwinCheckedBase 32768 53837869 widths3
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [checked3] at h
  simpa [widths3] using h.symm

theorem join_0_0 : (twinPrimeSegment 53739565 53805101).card = 264 := by
  simpa using combineTwinPrimeSegments (by decide : 53739565 ≤ 53772333)
    (by decide : 53772333 ≤ 53805101) block0 block1

theorem join_0_1 : (twinPrimeSegment 53805101 53870637).card = 270 := by
  simpa using combineTwinPrimeSegments (by decide : 53805101 ≤ 53837869)
    (by decide : 53837869 ≤ 53870637) block2 block3

theorem join_1_0 : (twinPrimeSegment 53739565 53870637).card = 534 := by
  simpa using combineTwinPrimeSegments (by decide : 53739565 ≤ 53805101)
    (by decide : 53805101 ≤ 53870637) join_0_0 join_0_1

theorem total : (twinPrimeSegment 53739565 53870637).card = 534 := join_1_0

end S025C10
end Sude.GeneratedTwinScan
