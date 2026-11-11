import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinGeometricScan

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S026C02
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def widths0 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked0 : geometricActiveStreamingTwinScan finiteTwinCheckedBase 54788141 widths0 = 126 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 54788141 54820909).card = 126 := by
  have h := geometricActiveStreamingTwinScan_spec finiteTwinCheckedBase 32768 54788141 widths0
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [checked0] at h
  simpa [widths0] using h.symm

def widths1 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked1 : geometricActiveStreamingTwinScan finiteTwinCheckedBase 54820909 widths1 = 144 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 54820909 54853677).card = 144 := by
  have h := geometricActiveStreamingTwinScan_spec finiteTwinCheckedBase 32768 54820909 widths1
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [checked1] at h
  simpa [widths1] using h.symm

def widths2 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked2 : geometricActiveStreamingTwinScan finiteTwinCheckedBase 54853677 widths2 = 136 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 54853677 54886445).card = 136 := by
  have h := geometricActiveStreamingTwinScan_spec finiteTwinCheckedBase 32768 54853677 widths2
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [checked2] at h
  simpa [widths2] using h.symm

def widths3 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked3 : geometricActiveStreamingTwinScan finiteTwinCheckedBase 54886445 widths3 = 150 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 54886445 54919213).card = 150 := by
  have h := geometricActiveStreamingTwinScan_spec finiteTwinCheckedBase 32768 54886445 widths3
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [checked3] at h
  simpa [widths3] using h.symm

theorem join_0_0 : (twinPrimeSegment 54788141 54853677).card = 270 := by
  simpa using combineTwinPrimeSegments (by decide : 54788141 ≤ 54820909)
    (by decide : 54820909 ≤ 54853677) block0 block1

theorem join_0_1 : (twinPrimeSegment 54853677 54919213).card = 286 := by
  simpa using combineTwinPrimeSegments (by decide : 54853677 ≤ 54886445)
    (by decide : 54886445 ≤ 54919213) block2 block3

theorem join_1_0 : (twinPrimeSegment 54788141 54919213).card = 556 := by
  simpa using combineTwinPrimeSegments (by decide : 54788141 ≤ 54853677)
    (by decide : 54853677 ≤ 54919213) join_0_0 join_0_1

theorem total : (twinPrimeSegment 54788141 54919213).card = 556 := join_1_0

end S026C02
end Sude.GeneratedTwinScan
