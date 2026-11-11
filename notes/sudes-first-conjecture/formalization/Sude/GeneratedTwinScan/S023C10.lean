import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinGeometricScan

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S023C10
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def widths0 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked0 : geometricActiveStreamingTwinScan finiteTwinCheckedBase 49545261 widths0 = 150 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 49545261 49578029).card = 150 := by
  have h := geometricActiveStreamingTwinScan_spec finiteTwinCheckedBase 32768 49545261 widths0
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [checked0] at h
  simpa [widths0] using h.symm

def widths1 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked1 : geometricActiveStreamingTwinScan finiteTwinCheckedBase 49578029 widths1 = 144 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 49578029 49610797).card = 144 := by
  have h := geometricActiveStreamingTwinScan_spec finiteTwinCheckedBase 32768 49578029 widths1
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [checked1] at h
  simpa [widths1] using h.symm

def widths2 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked2 : geometricActiveStreamingTwinScan finiteTwinCheckedBase 49610797 widths2 = 145 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 49610797 49643565).card = 145 := by
  have h := geometricActiveStreamingTwinScan_spec finiteTwinCheckedBase 32768 49610797 widths2
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [checked2] at h
  simpa [widths2] using h.symm

def widths3 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked3 : geometricActiveStreamingTwinScan finiteTwinCheckedBase 49643565 widths3 = 122 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 49643565 49676333).card = 122 := by
  have h := geometricActiveStreamingTwinScan_spec finiteTwinCheckedBase 32768 49643565 widths3
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [checked3] at h
  simpa [widths3] using h.symm

theorem join_0_0 : (twinPrimeSegment 49545261 49610797).card = 294 := by
  simpa using combineTwinPrimeSegments (by decide : 49545261 ≤ 49578029)
    (by decide : 49578029 ≤ 49610797) block0 block1

theorem join_0_1 : (twinPrimeSegment 49610797 49676333).card = 267 := by
  simpa using combineTwinPrimeSegments (by decide : 49610797 ≤ 49643565)
    (by decide : 49643565 ≤ 49676333) block2 block3

theorem join_1_0 : (twinPrimeSegment 49545261 49676333).card = 561 := by
  simpa using combineTwinPrimeSegments (by decide : 49545261 ≤ 49610797)
    (by decide : 49610797 ≤ 49676333) join_0_0 join_0_1

theorem total : (twinPrimeSegment 49545261 49676333).card = 561 := join_1_0

end S023C10
end Sude.GeneratedTwinScan
