import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinGeometricScan

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S019C02
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def widths0 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked0 : geometricActiveStreamingTwinScan finiteTwinCheckedBase 40108077 widths0 = 131 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 40108077 40140845).card = 131 := by
  have h := geometricActiveStreamingTwinScan_spec finiteTwinCheckedBase 32768 40108077 widths0
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [checked0] at h
  simpa [widths0] using h.symm

def widths1 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked1 : geometricActiveStreamingTwinScan finiteTwinCheckedBase 40140845 widths1 = 146 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 40140845 40173613).card = 146 := by
  have h := geometricActiveStreamingTwinScan_spec finiteTwinCheckedBase 32768 40140845 widths1
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [checked1] at h
  simpa [widths1] using h.symm

def widths2 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked2 : geometricActiveStreamingTwinScan finiteTwinCheckedBase 40173613 widths2 = 144 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 40173613 40206381).card = 144 := by
  have h := geometricActiveStreamingTwinScan_spec finiteTwinCheckedBase 32768 40173613 widths2
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [checked2] at h
  simpa [widths2] using h.symm

def widths3 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked3 : geometricActiveStreamingTwinScan finiteTwinCheckedBase 40206381 widths3 = 139 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 40206381 40239149).card = 139 := by
  have h := geometricActiveStreamingTwinScan_spec finiteTwinCheckedBase 32768 40206381 widths3
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [checked3] at h
  simpa [widths3] using h.symm

theorem join_0_0 : (twinPrimeSegment 40108077 40173613).card = 277 := by
  simpa using combineTwinPrimeSegments (by decide : 40108077 ≤ 40140845)
    (by decide : 40140845 ≤ 40173613) block0 block1

theorem join_0_1 : (twinPrimeSegment 40173613 40239149).card = 283 := by
  simpa using combineTwinPrimeSegments (by decide : 40173613 ≤ 40206381)
    (by decide : 40206381 ≤ 40239149) block2 block3

theorem join_1_0 : (twinPrimeSegment 40108077 40239149).card = 560 := by
  simpa using combineTwinPrimeSegments (by decide : 40108077 ≤ 40173613)
    (by decide : 40173613 ≤ 40239149) join_0_0 join_0_1

theorem total : (twinPrimeSegment 40108077 40239149).card = 560 := join_1_0

end S019C02
end Sude.GeneratedTwinScan
