import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinGeometricScan

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S015C03
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def widths0 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked0 : geometricActiveStreamingTwinScan finiteTwinCheckedBase 31850541 widths0 = 162 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 31850541 31883309).card = 162 := by
  have h := geometricActiveStreamingTwinScan_spec finiteTwinCheckedBase 32768 31850541 widths0
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [checked0] at h
  simpa [widths0] using h.symm

def widths1 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked1 : geometricActiveStreamingTwinScan finiteTwinCheckedBase 31883309 widths1 = 122 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 31883309 31916077).card = 122 := by
  have h := geometricActiveStreamingTwinScan_spec finiteTwinCheckedBase 32768 31883309 widths1
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [checked1] at h
  simpa [widths1] using h.symm

def widths2 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked2 : geometricActiveStreamingTwinScan finiteTwinCheckedBase 31916077 widths2 = 156 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 31916077 31948845).card = 156 := by
  have h := geometricActiveStreamingTwinScan_spec finiteTwinCheckedBase 32768 31916077 widths2
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [checked2] at h
  simpa [widths2] using h.symm

def widths3 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked3 : geometricActiveStreamingTwinScan finiteTwinCheckedBase 31948845 widths3 = 152 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 31948845 31981613).card = 152 := by
  have h := geometricActiveStreamingTwinScan_spec finiteTwinCheckedBase 32768 31948845 widths3
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [checked3] at h
  simpa [widths3] using h.symm

theorem join_0_0 : (twinPrimeSegment 31850541 31916077).card = 284 := by
  simpa using combineTwinPrimeSegments (by decide : 31850541 ≤ 31883309)
    (by decide : 31883309 ≤ 31916077) block0 block1

theorem join_0_1 : (twinPrimeSegment 31916077 31981613).card = 308 := by
  simpa using combineTwinPrimeSegments (by decide : 31916077 ≤ 31948845)
    (by decide : 31948845 ≤ 31981613) block2 block3

theorem join_1_0 : (twinPrimeSegment 31850541 31981613).card = 592 := by
  simpa using combineTwinPrimeSegments (by decide : 31850541 ≤ 31916077)
    (by decide : 31916077 ≤ 31981613) join_0_0 join_0_1

theorem total : (twinPrimeSegment 31850541 31981613).card = 592 := join_1_0

end S015C03
end Sude.GeneratedTwinScan
