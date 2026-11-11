import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinGeometricScan

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S025C07
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def widths0 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked0 : geometricActiveStreamingTwinScan finiteTwinCheckedBase 53346349 widths0 = 136 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 53346349 53379117).card = 136 := by
  have h := geometricActiveStreamingTwinScan_spec finiteTwinCheckedBase 32768 53346349 widths0
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [checked0] at h
  simpa [widths0] using h.symm

def widths1 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked1 : geometricActiveStreamingTwinScan finiteTwinCheckedBase 53379117 widths1 = 144 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 53379117 53411885).card = 144 := by
  have h := geometricActiveStreamingTwinScan_spec finiteTwinCheckedBase 32768 53379117 widths1
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [checked1] at h
  simpa [widths1] using h.symm

def widths2 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked2 : geometricActiveStreamingTwinScan finiteTwinCheckedBase 53411885 widths2 = 138 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 53411885 53444653).card = 138 := by
  have h := geometricActiveStreamingTwinScan_spec finiteTwinCheckedBase 32768 53411885 widths2
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [checked2] at h
  simpa [widths2] using h.symm

def widths3 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked3 : geometricActiveStreamingTwinScan finiteTwinCheckedBase 53444653 widths3 = 130 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 53444653 53477421).card = 130 := by
  have h := geometricActiveStreamingTwinScan_spec finiteTwinCheckedBase 32768 53444653 widths3
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [checked3] at h
  simpa [widths3] using h.symm

theorem join_0_0 : (twinPrimeSegment 53346349 53411885).card = 280 := by
  simpa using combineTwinPrimeSegments (by decide : 53346349 ≤ 53379117)
    (by decide : 53379117 ≤ 53411885) block0 block1

theorem join_0_1 : (twinPrimeSegment 53411885 53477421).card = 268 := by
  simpa using combineTwinPrimeSegments (by decide : 53411885 ≤ 53444653)
    (by decide : 53444653 ≤ 53477421) block2 block3

theorem join_1_0 : (twinPrimeSegment 53346349 53477421).card = 548 := by
  simpa using combineTwinPrimeSegments (by decide : 53346349 ≤ 53411885)
    (by decide : 53411885 ≤ 53477421) join_0_0 join_0_1

theorem total : (twinPrimeSegment 53346349 53477421).card = 548 := join_1_0

end S025C07
end Sude.GeneratedTwinScan
