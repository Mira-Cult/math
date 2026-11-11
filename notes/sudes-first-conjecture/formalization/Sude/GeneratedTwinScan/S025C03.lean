import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinGeometricScan

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S025C03
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def widths0 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked0 : geometricActiveStreamingTwinScan finiteTwinCheckedBase 52822061 widths0 = 142 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 52822061 52854829).card = 142 := by
  have h := geometricActiveStreamingTwinScan_spec finiteTwinCheckedBase 32768 52822061 widths0
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [checked0] at h
  simpa [widths0] using h.symm

def widths1 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked1 : geometricActiveStreamingTwinScan finiteTwinCheckedBase 52854829 widths1 = 144 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 52854829 52887597).card = 144 := by
  have h := geometricActiveStreamingTwinScan_spec finiteTwinCheckedBase 32768 52854829 widths1
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [checked1] at h
  simpa [widths1] using h.symm

def widths2 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked2 : geometricActiveStreamingTwinScan finiteTwinCheckedBase 52887597 widths2 = 133 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 52887597 52920365).card = 133 := by
  have h := geometricActiveStreamingTwinScan_spec finiteTwinCheckedBase 32768 52887597 widths2
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [checked2] at h
  simpa [widths2] using h.symm

def widths3 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked3 : geometricActiveStreamingTwinScan finiteTwinCheckedBase 52920365 widths3 = 151 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 52920365 52953133).card = 151 := by
  have h := geometricActiveStreamingTwinScan_spec finiteTwinCheckedBase 32768 52920365 widths3
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [checked3] at h
  simpa [widths3] using h.symm

theorem join_0_0 : (twinPrimeSegment 52822061 52887597).card = 286 := by
  simpa using combineTwinPrimeSegments (by decide : 52822061 ≤ 52854829)
    (by decide : 52854829 ≤ 52887597) block0 block1

theorem join_0_1 : (twinPrimeSegment 52887597 52953133).card = 284 := by
  simpa using combineTwinPrimeSegments (by decide : 52887597 ≤ 52920365)
    (by decide : 52920365 ≤ 52953133) block2 block3

theorem join_1_0 : (twinPrimeSegment 52822061 52953133).card = 570 := by
  simpa using combineTwinPrimeSegments (by decide : 52822061 ≤ 52887597)
    (by decide : 52887597 ≤ 52953133) join_0_0 join_0_1

theorem total : (twinPrimeSegment 52822061 52953133).card = 570 := join_1_0

end S025C03
end Sude.GeneratedTwinScan
