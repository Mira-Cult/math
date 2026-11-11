import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinGeometricScan

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S020C02
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def widths0 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked0 : geometricActiveStreamingTwinScan finiteTwinCheckedBase 42205229 widths0 = 136 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 42205229 42237997).card = 136 := by
  have h := geometricActiveStreamingTwinScan_spec finiteTwinCheckedBase 32768 42205229 widths0
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [checked0] at h
  simpa [widths0] using h.symm

def widths1 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked1 : geometricActiveStreamingTwinScan finiteTwinCheckedBase 42237997 widths1 = 144 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 42237997 42270765).card = 144 := by
  have h := geometricActiveStreamingTwinScan_spec finiteTwinCheckedBase 32768 42237997 widths1
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [checked1] at h
  simpa [widths1] using h.symm

def widths2 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked2 : geometricActiveStreamingTwinScan finiteTwinCheckedBase 42270765 widths2 = 143 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 42270765 42303533).card = 143 := by
  have h := geometricActiveStreamingTwinScan_spec finiteTwinCheckedBase 32768 42270765 widths2
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [checked2] at h
  simpa [widths2] using h.symm

def widths3 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked3 : geometricActiveStreamingTwinScan finiteTwinCheckedBase 42303533 widths3 = 136 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 42303533 42336301).card = 136 := by
  have h := geometricActiveStreamingTwinScan_spec finiteTwinCheckedBase 32768 42303533 widths3
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [checked3] at h
  simpa [widths3] using h.symm

theorem join_0_0 : (twinPrimeSegment 42205229 42270765).card = 280 := by
  simpa using combineTwinPrimeSegments (by decide : 42205229 ≤ 42237997)
    (by decide : 42237997 ≤ 42270765) block0 block1

theorem join_0_1 : (twinPrimeSegment 42270765 42336301).card = 279 := by
  simpa using combineTwinPrimeSegments (by decide : 42270765 ≤ 42303533)
    (by decide : 42303533 ≤ 42336301) block2 block3

theorem join_1_0 : (twinPrimeSegment 42205229 42336301).card = 559 := by
  simpa using combineTwinPrimeSegments (by decide : 42205229 ≤ 42270765)
    (by decide : 42270765 ≤ 42336301) join_0_0 join_0_1

theorem total : (twinPrimeSegment 42205229 42336301).card = 559 := join_1_0

end S020C02
end Sude.GeneratedTwinScan
