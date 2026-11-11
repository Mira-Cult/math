import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinGeometricScan

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S025C00
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def widths0 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked0 : geometricActiveStreamingTwinScan finiteTwinCheckedBase 52428845 widths0 = 146 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 52428845 52461613).card = 146 := by
  have h := geometricActiveStreamingTwinScan_spec finiteTwinCheckedBase 32768 52428845 widths0
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [checked0] at h
  simpa [widths0] using h.symm

def widths1 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked1 : geometricActiveStreamingTwinScan finiteTwinCheckedBase 52461613 widths1 = 141 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 52461613 52494381).card = 141 := by
  have h := geometricActiveStreamingTwinScan_spec finiteTwinCheckedBase 32768 52461613 widths1
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [checked1] at h
  simpa [widths1] using h.symm

def widths2 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked2 : geometricActiveStreamingTwinScan finiteTwinCheckedBase 52494381 widths2 = 126 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 52494381 52527149).card = 126 := by
  have h := geometricActiveStreamingTwinScan_spec finiteTwinCheckedBase 32768 52494381 widths2
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [checked2] at h
  simpa [widths2] using h.symm

def widths3 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked3 : geometricActiveStreamingTwinScan finiteTwinCheckedBase 52527149 widths3 = 128 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 52527149 52559917).card = 128 := by
  have h := geometricActiveStreamingTwinScan_spec finiteTwinCheckedBase 32768 52527149 widths3
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [checked3] at h
  simpa [widths3] using h.symm

theorem join_0_0 : (twinPrimeSegment 52428845 52494381).card = 287 := by
  simpa using combineTwinPrimeSegments (by decide : 52428845 ≤ 52461613)
    (by decide : 52461613 ≤ 52494381) block0 block1

theorem join_0_1 : (twinPrimeSegment 52494381 52559917).card = 254 := by
  simpa using combineTwinPrimeSegments (by decide : 52494381 ≤ 52527149)
    (by decide : 52527149 ≤ 52559917) block2 block3

theorem join_1_0 : (twinPrimeSegment 52428845 52559917).card = 541 := by
  simpa using combineTwinPrimeSegments (by decide : 52428845 ≤ 52494381)
    (by decide : 52494381 ≤ 52559917) join_0_0 join_0_1

theorem total : (twinPrimeSegment 52428845 52559917).card = 541 := join_1_0

end S025C00
end Sude.GeneratedTwinScan
