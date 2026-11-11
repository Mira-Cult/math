import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinGeometricScan

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S024C11
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def widths0 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked0 : geometricActiveStreamingTwinScan finiteTwinCheckedBase 51773485 widths0 = 148 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 51773485 51806253).card = 148 := by
  have h := geometricActiveStreamingTwinScan_spec finiteTwinCheckedBase 32768 51773485 widths0
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [checked0] at h
  simpa [widths0] using h.symm

def widths1 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked1 : geometricActiveStreamingTwinScan finiteTwinCheckedBase 51806253 widths1 = 130 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 51806253 51839021).card = 130 := by
  have h := geometricActiveStreamingTwinScan_spec finiteTwinCheckedBase 32768 51806253 widths1
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [checked1] at h
  simpa [widths1] using h.symm

def widths2 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked2 : geometricActiveStreamingTwinScan finiteTwinCheckedBase 51839021 widths2 = 136 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 51839021 51871789).card = 136 := by
  have h := geometricActiveStreamingTwinScan_spec finiteTwinCheckedBase 32768 51839021 widths2
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [checked2] at h
  simpa [widths2] using h.symm

def widths3 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked3 : geometricActiveStreamingTwinScan finiteTwinCheckedBase 51871789 widths3 = 135 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 51871789 51904557).card = 135 := by
  have h := geometricActiveStreamingTwinScan_spec finiteTwinCheckedBase 32768 51871789 widths3
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [checked3] at h
  simpa [widths3] using h.symm

theorem join_0_0 : (twinPrimeSegment 51773485 51839021).card = 278 := by
  simpa using combineTwinPrimeSegments (by decide : 51773485 ≤ 51806253)
    (by decide : 51806253 ≤ 51839021) block0 block1

theorem join_0_1 : (twinPrimeSegment 51839021 51904557).card = 271 := by
  simpa using combineTwinPrimeSegments (by decide : 51839021 ≤ 51871789)
    (by decide : 51871789 ≤ 51904557) block2 block3

theorem join_1_0 : (twinPrimeSegment 51773485 51904557).card = 549 := by
  simpa using combineTwinPrimeSegments (by decide : 51773485 ≤ 51839021)
    (by decide : 51839021 ≤ 51904557) join_0_0 join_0_1

theorem total : (twinPrimeSegment 51773485 51904557).card = 549 := join_1_0

end S024C11
end Sude.GeneratedTwinScan
