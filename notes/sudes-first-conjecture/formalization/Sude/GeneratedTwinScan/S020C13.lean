import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinGeometricScan

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S020C13
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def widths0 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked0 : geometricActiveStreamingTwinScan finiteTwinCheckedBase 43647021 widths0 = 125 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 43647021 43679789).card = 125 := by
  have h := geometricActiveStreamingTwinScan_spec finiteTwinCheckedBase 32768 43647021 widths0
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [checked0] at h
  simpa [widths0] using h.symm

def widths1 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked1 : geometricActiveStreamingTwinScan finiteTwinCheckedBase 43679789 widths1 = 148 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 43679789 43712557).card = 148 := by
  have h := geometricActiveStreamingTwinScan_spec finiteTwinCheckedBase 32768 43679789 widths1
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [checked1] at h
  simpa [widths1] using h.symm

def widths2 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked2 : geometricActiveStreamingTwinScan finiteTwinCheckedBase 43712557 widths2 = 129 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 43712557 43745325).card = 129 := by
  have h := geometricActiveStreamingTwinScan_spec finiteTwinCheckedBase 32768 43712557 widths2
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [checked2] at h
  simpa [widths2] using h.symm

def widths3 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked3 : geometricActiveStreamingTwinScan finiteTwinCheckedBase 43745325 widths3 = 123 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 43745325 43778093).card = 123 := by
  have h := geometricActiveStreamingTwinScan_spec finiteTwinCheckedBase 32768 43745325 widths3
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [checked3] at h
  simpa [widths3] using h.symm

theorem join_0_0 : (twinPrimeSegment 43647021 43712557).card = 273 := by
  simpa using combineTwinPrimeSegments (by decide : 43647021 ≤ 43679789)
    (by decide : 43679789 ≤ 43712557) block0 block1

theorem join_0_1 : (twinPrimeSegment 43712557 43778093).card = 252 := by
  simpa using combineTwinPrimeSegments (by decide : 43712557 ≤ 43745325)
    (by decide : 43745325 ≤ 43778093) block2 block3

theorem join_1_0 : (twinPrimeSegment 43647021 43778093).card = 525 := by
  simpa using combineTwinPrimeSegments (by decide : 43647021 ≤ 43712557)
    (by decide : 43712557 ≤ 43778093) join_0_0 join_0_1

theorem total : (twinPrimeSegment 43647021 43778093).card = 525 := join_1_0

end S020C13
end Sude.GeneratedTwinScan
