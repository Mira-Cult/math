import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinGeometricScan

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S027C05
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def widths0 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked0 : geometricActiveStreamingTwinScan finiteTwinCheckedBase 57278509 widths0 = 129 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 57278509 57311277).card = 129 := by
  have h := geometricActiveStreamingTwinScan_spec finiteTwinCheckedBase 32768 57278509 widths0
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [checked0] at h
  simpa [widths0] using h.symm

def widths1 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked1 : geometricActiveStreamingTwinScan finiteTwinCheckedBase 57311277 widths1 = 134 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 57311277 57344045).card = 134 := by
  have h := geometricActiveStreamingTwinScan_spec finiteTwinCheckedBase 32768 57311277 widths1
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [checked1] at h
  simpa [widths1] using h.symm

def widths2 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked2 : geometricActiveStreamingTwinScan finiteTwinCheckedBase 57344045 widths2 = 136 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 57344045 57376813).card = 136 := by
  have h := geometricActiveStreamingTwinScan_spec finiteTwinCheckedBase 32768 57344045 widths2
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [checked2] at h
  simpa [widths2] using h.symm

def widths3 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked3 : geometricActiveStreamingTwinScan finiteTwinCheckedBase 57376813 widths3 = 148 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 57376813 57409581).card = 148 := by
  have h := geometricActiveStreamingTwinScan_spec finiteTwinCheckedBase 32768 57376813 widths3
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [checked3] at h
  simpa [widths3] using h.symm

theorem join_0_0 : (twinPrimeSegment 57278509 57344045).card = 263 := by
  simpa using combineTwinPrimeSegments (by decide : 57278509 ≤ 57311277)
    (by decide : 57311277 ≤ 57344045) block0 block1

theorem join_0_1 : (twinPrimeSegment 57344045 57409581).card = 284 := by
  simpa using combineTwinPrimeSegments (by decide : 57344045 ≤ 57376813)
    (by decide : 57376813 ≤ 57409581) block2 block3

theorem join_1_0 : (twinPrimeSegment 57278509 57409581).card = 547 := by
  simpa using combineTwinPrimeSegments (by decide : 57278509 ≤ 57344045)
    (by decide : 57344045 ≤ 57409581) join_0_0 join_0_1

theorem total : (twinPrimeSegment 57278509 57409581).card = 547 := join_1_0

end S027C05
end Sude.GeneratedTwinScan
