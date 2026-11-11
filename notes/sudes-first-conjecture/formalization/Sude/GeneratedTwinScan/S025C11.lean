import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinGeometricScan

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S025C11
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def widths0 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked0 : geometricActiveStreamingTwinScan finiteTwinCheckedBase 53870637 widths0 = 150 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 53870637 53903405).card = 150 := by
  have h := geometricActiveStreamingTwinScan_spec finiteTwinCheckedBase 32768 53870637 widths0
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [checked0] at h
  simpa [widths0] using h.symm

def widths1 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked1 : geometricActiveStreamingTwinScan finiteTwinCheckedBase 53903405 widths1 = 138 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 53903405 53936173).card = 138 := by
  have h := geometricActiveStreamingTwinScan_spec finiteTwinCheckedBase 32768 53903405 widths1
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [checked1] at h
  simpa [widths1] using h.symm

def widths2 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked2 : geometricActiveStreamingTwinScan finiteTwinCheckedBase 53936173 widths2 = 133 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 53936173 53968941).card = 133 := by
  have h := geometricActiveStreamingTwinScan_spec finiteTwinCheckedBase 32768 53936173 widths2
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [checked2] at h
  simpa [widths2] using h.symm

def widths3 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked3 : geometricActiveStreamingTwinScan finiteTwinCheckedBase 53968941 widths3 = 144 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 53968941 54001709).card = 144 := by
  have h := geometricActiveStreamingTwinScan_spec finiteTwinCheckedBase 32768 53968941 widths3
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [checked3] at h
  simpa [widths3] using h.symm

theorem join_0_0 : (twinPrimeSegment 53870637 53936173).card = 288 := by
  simpa using combineTwinPrimeSegments (by decide : 53870637 ≤ 53903405)
    (by decide : 53903405 ≤ 53936173) block0 block1

theorem join_0_1 : (twinPrimeSegment 53936173 54001709).card = 277 := by
  simpa using combineTwinPrimeSegments (by decide : 53936173 ≤ 53968941)
    (by decide : 53968941 ≤ 54001709) block2 block3

theorem join_1_0 : (twinPrimeSegment 53870637 54001709).card = 565 := by
  simpa using combineTwinPrimeSegments (by decide : 53870637 ≤ 53936173)
    (by decide : 53936173 ≤ 54001709) join_0_0 join_0_1

theorem total : (twinPrimeSegment 53870637 54001709).card = 565 := join_1_0

end S025C11
end Sude.GeneratedTwinScan
