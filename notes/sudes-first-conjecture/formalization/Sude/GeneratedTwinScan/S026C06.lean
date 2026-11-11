import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinGeometricScan

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S026C06
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def widths0 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked0 : geometricActiveStreamingTwinScan finiteTwinCheckedBase 55312429 widths0 = 153 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 55312429 55345197).card = 153 := by
  have h := geometricActiveStreamingTwinScan_spec finiteTwinCheckedBase 32768 55312429 widths0
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [checked0] at h
  simpa [widths0] using h.symm

def widths1 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked1 : geometricActiveStreamingTwinScan finiteTwinCheckedBase 55345197 widths1 = 129 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 55345197 55377965).card = 129 := by
  have h := geometricActiveStreamingTwinScan_spec finiteTwinCheckedBase 32768 55345197 widths1
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [checked1] at h
  simpa [widths1] using h.symm

def widths2 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked2 : geometricActiveStreamingTwinScan finiteTwinCheckedBase 55377965 widths2 = 141 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 55377965 55410733).card = 141 := by
  have h := geometricActiveStreamingTwinScan_spec finiteTwinCheckedBase 32768 55377965 widths2
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [checked2] at h
  simpa [widths2] using h.symm

def widths3 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked3 : geometricActiveStreamingTwinScan finiteTwinCheckedBase 55410733 widths3 = 147 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 55410733 55443501).card = 147 := by
  have h := geometricActiveStreamingTwinScan_spec finiteTwinCheckedBase 32768 55410733 widths3
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [checked3] at h
  simpa [widths3] using h.symm

theorem join_0_0 : (twinPrimeSegment 55312429 55377965).card = 282 := by
  simpa using combineTwinPrimeSegments (by decide : 55312429 ≤ 55345197)
    (by decide : 55345197 ≤ 55377965) block0 block1

theorem join_0_1 : (twinPrimeSegment 55377965 55443501).card = 288 := by
  simpa using combineTwinPrimeSegments (by decide : 55377965 ≤ 55410733)
    (by decide : 55410733 ≤ 55443501) block2 block3

theorem join_1_0 : (twinPrimeSegment 55312429 55443501).card = 570 := by
  simpa using combineTwinPrimeSegments (by decide : 55312429 ≤ 55377965)
    (by decide : 55377965 ≤ 55443501) join_0_0 join_0_1

theorem total : (twinPrimeSegment 55312429 55443501).card = 570 := join_1_0

end S026C06
end Sude.GeneratedTwinScan
