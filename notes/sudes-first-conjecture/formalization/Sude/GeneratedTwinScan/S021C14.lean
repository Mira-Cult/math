import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinGeometricScan

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S021C14
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def widths0 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked0 : geometricActiveStreamingTwinScan finiteTwinCheckedBase 45875245 widths0 = 138 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 45875245 45908013).card = 138 := by
  have h := geometricActiveStreamingTwinScan_spec finiteTwinCheckedBase 32768 45875245 widths0
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [checked0] at h
  simpa [widths0] using h.symm

def widths1 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked1 : geometricActiveStreamingTwinScan finiteTwinCheckedBase 45908013 widths1 = 138 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 45908013 45940781).card = 138 := by
  have h := geometricActiveStreamingTwinScan_spec finiteTwinCheckedBase 32768 45908013 widths1
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [checked1] at h
  simpa [widths1] using h.symm

def widths2 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked2 : geometricActiveStreamingTwinScan finiteTwinCheckedBase 45940781 widths2 = 136 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 45940781 45973549).card = 136 := by
  have h := geometricActiveStreamingTwinScan_spec finiteTwinCheckedBase 32768 45940781 widths2
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [checked2] at h
  simpa [widths2] using h.symm

def widths3 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked3 : geometricActiveStreamingTwinScan finiteTwinCheckedBase 45973549 widths3 = 137 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 45973549 46006317).card = 137 := by
  have h := geometricActiveStreamingTwinScan_spec finiteTwinCheckedBase 32768 45973549 widths3
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [checked3] at h
  simpa [widths3] using h.symm

theorem join_0_0 : (twinPrimeSegment 45875245 45940781).card = 276 := by
  simpa using combineTwinPrimeSegments (by decide : 45875245 ≤ 45908013)
    (by decide : 45908013 ≤ 45940781) block0 block1

theorem join_0_1 : (twinPrimeSegment 45940781 46006317).card = 273 := by
  simpa using combineTwinPrimeSegments (by decide : 45940781 ≤ 45973549)
    (by decide : 45973549 ≤ 46006317) block2 block3

theorem join_1_0 : (twinPrimeSegment 45875245 46006317).card = 549 := by
  simpa using combineTwinPrimeSegments (by decide : 45875245 ≤ 45940781)
    (by decide : 45940781 ≤ 46006317) join_0_0 join_0_1

theorem total : (twinPrimeSegment 45875245 46006317).card = 549 := join_1_0

end S021C14
end Sude.GeneratedTwinScan
