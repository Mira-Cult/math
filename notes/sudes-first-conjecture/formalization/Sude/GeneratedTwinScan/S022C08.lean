import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinGeometricScan

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S022C08
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def widths0 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked0 : geometricActiveStreamingTwinScan finiteTwinCheckedBase 47185965 widths0 = 151 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 47185965 47218733).card = 151 := by
  have h := geometricActiveStreamingTwinScan_spec finiteTwinCheckedBase 32768 47185965 widths0
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [checked0] at h
  simpa [widths0] using h.symm

def widths1 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked1 : geometricActiveStreamingTwinScan finiteTwinCheckedBase 47218733 widths1 = 133 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 47218733 47251501).card = 133 := by
  have h := geometricActiveStreamingTwinScan_spec finiteTwinCheckedBase 32768 47218733 widths1
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [checked1] at h
  simpa [widths1] using h.symm

def widths2 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked2 : geometricActiveStreamingTwinScan finiteTwinCheckedBase 47251501 widths2 = 134 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 47251501 47284269).card = 134 := by
  have h := geometricActiveStreamingTwinScan_spec finiteTwinCheckedBase 32768 47251501 widths2
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [checked2] at h
  simpa [widths2] using h.symm

def widths3 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked3 : geometricActiveStreamingTwinScan finiteTwinCheckedBase 47284269 widths3 = 131 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 47284269 47317037).card = 131 := by
  have h := geometricActiveStreamingTwinScan_spec finiteTwinCheckedBase 32768 47284269 widths3
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [checked3] at h
  simpa [widths3] using h.symm

theorem join_0_0 : (twinPrimeSegment 47185965 47251501).card = 284 := by
  simpa using combineTwinPrimeSegments (by decide : 47185965 ≤ 47218733)
    (by decide : 47218733 ≤ 47251501) block0 block1

theorem join_0_1 : (twinPrimeSegment 47251501 47317037).card = 265 := by
  simpa using combineTwinPrimeSegments (by decide : 47251501 ≤ 47284269)
    (by decide : 47284269 ≤ 47317037) block2 block3

theorem join_1_0 : (twinPrimeSegment 47185965 47317037).card = 549 := by
  simpa using combineTwinPrimeSegments (by decide : 47185965 ≤ 47251501)
    (by decide : 47251501 ≤ 47317037) join_0_0 join_0_1

theorem total : (twinPrimeSegment 47185965 47317037).card = 549 := join_1_0

end S022C08
end Sude.GeneratedTwinScan
