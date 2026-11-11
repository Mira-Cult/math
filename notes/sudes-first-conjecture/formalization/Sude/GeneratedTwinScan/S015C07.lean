import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinGeometricScan

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S015C07
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def widths0 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked0 : geometricActiveStreamingTwinScan finiteTwinCheckedBase 32374829 widths0 = 132 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 32374829 32407597).card = 132 := by
  have h := geometricActiveStreamingTwinScan_spec finiteTwinCheckedBase 32768 32374829 widths0
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [checked0] at h
  simpa [widths0] using h.symm

def widths1 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked1 : geometricActiveStreamingTwinScan finiteTwinCheckedBase 32407597 widths1 = 123 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 32407597 32440365).card = 123 := by
  have h := geometricActiveStreamingTwinScan_spec finiteTwinCheckedBase 32768 32407597 widths1
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [checked1] at h
  simpa [widths1] using h.symm

def widths2 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked2 : geometricActiveStreamingTwinScan finiteTwinCheckedBase 32440365 widths2 = 145 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 32440365 32473133).card = 145 := by
  have h := geometricActiveStreamingTwinScan_spec finiteTwinCheckedBase 32768 32440365 widths2
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [checked2] at h
  simpa [widths2] using h.symm

def widths3 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked3 : geometricActiveStreamingTwinScan finiteTwinCheckedBase 32473133 widths3 = 140 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 32473133 32505901).card = 140 := by
  have h := geometricActiveStreamingTwinScan_spec finiteTwinCheckedBase 32768 32473133 widths3
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [checked3] at h
  simpa [widths3] using h.symm

theorem join_0_0 : (twinPrimeSegment 32374829 32440365).card = 255 := by
  simpa using combineTwinPrimeSegments (by decide : 32374829 ≤ 32407597)
    (by decide : 32407597 ≤ 32440365) block0 block1

theorem join_0_1 : (twinPrimeSegment 32440365 32505901).card = 285 := by
  simpa using combineTwinPrimeSegments (by decide : 32440365 ≤ 32473133)
    (by decide : 32473133 ≤ 32505901) block2 block3

theorem join_1_0 : (twinPrimeSegment 32374829 32505901).card = 540 := by
  simpa using combineTwinPrimeSegments (by decide : 32374829 ≤ 32440365)
    (by decide : 32440365 ≤ 32505901) join_0_0 join_0_1

theorem total : (twinPrimeSegment 32374829 32505901).card = 540 := join_1_0

end S015C07
end Sude.GeneratedTwinScan
