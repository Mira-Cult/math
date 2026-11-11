import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinGeometricScan

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S026C07
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def widths0 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked0 : geometricActiveStreamingTwinScan finiteTwinCheckedBase 55443501 widths0 = 139 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 55443501 55476269).card = 139 := by
  have h := geometricActiveStreamingTwinScan_spec finiteTwinCheckedBase 32768 55443501 widths0
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [checked0] at h
  simpa [widths0] using h.symm

def widths1 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked1 : geometricActiveStreamingTwinScan finiteTwinCheckedBase 55476269 widths1 = 136 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 55476269 55509037).card = 136 := by
  have h := geometricActiveStreamingTwinScan_spec finiteTwinCheckedBase 32768 55476269 widths1
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [checked1] at h
  simpa [widths1] using h.symm

def widths2 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked2 : geometricActiveStreamingTwinScan finiteTwinCheckedBase 55509037 widths2 = 124 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 55509037 55541805).card = 124 := by
  have h := geometricActiveStreamingTwinScan_spec finiteTwinCheckedBase 32768 55509037 widths2
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [checked2] at h
  simpa [widths2] using h.symm

def widths3 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked3 : geometricActiveStreamingTwinScan finiteTwinCheckedBase 55541805 widths3 = 131 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 55541805 55574573).card = 131 := by
  have h := geometricActiveStreamingTwinScan_spec finiteTwinCheckedBase 32768 55541805 widths3
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [checked3] at h
  simpa [widths3] using h.symm

theorem join_0_0 : (twinPrimeSegment 55443501 55509037).card = 275 := by
  simpa using combineTwinPrimeSegments (by decide : 55443501 ≤ 55476269)
    (by decide : 55476269 ≤ 55509037) block0 block1

theorem join_0_1 : (twinPrimeSegment 55509037 55574573).card = 255 := by
  simpa using combineTwinPrimeSegments (by decide : 55509037 ≤ 55541805)
    (by decide : 55541805 ≤ 55574573) block2 block3

theorem join_1_0 : (twinPrimeSegment 55443501 55574573).card = 530 := by
  simpa using combineTwinPrimeSegments (by decide : 55443501 ≤ 55509037)
    (by decide : 55509037 ≤ 55574573) join_0_0 join_0_1

theorem total : (twinPrimeSegment 55443501 55574573).card = 530 := join_1_0

end S026C07
end Sude.GeneratedTwinScan
