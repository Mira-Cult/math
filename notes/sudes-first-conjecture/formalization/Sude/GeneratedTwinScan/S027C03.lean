import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinGeometricScan

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S027C03
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def widths0 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked0 : geometricActiveStreamingTwinScan finiteTwinCheckedBase 57016365 widths0 = 115 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 57016365 57049133).card = 115 := by
  have h := geometricActiveStreamingTwinScan_spec finiteTwinCheckedBase 32768 57016365 widths0
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [checked0] at h
  simpa [widths0] using h.symm

def widths1 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked1 : geometricActiveStreamingTwinScan finiteTwinCheckedBase 57049133 widths1 = 135 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 57049133 57081901).card = 135 := by
  have h := geometricActiveStreamingTwinScan_spec finiteTwinCheckedBase 32768 57049133 widths1
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [checked1] at h
  simpa [widths1] using h.symm

def widths2 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked2 : geometricActiveStreamingTwinScan finiteTwinCheckedBase 57081901 widths2 = 141 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 57081901 57114669).card = 141 := by
  have h := geometricActiveStreamingTwinScan_spec finiteTwinCheckedBase 32768 57081901 widths2
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [checked2] at h
  simpa [widths2] using h.symm

def widths3 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked3 : geometricActiveStreamingTwinScan finiteTwinCheckedBase 57114669 widths3 = 149 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 57114669 57147437).card = 149 := by
  have h := geometricActiveStreamingTwinScan_spec finiteTwinCheckedBase 32768 57114669 widths3
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [checked3] at h
  simpa [widths3] using h.symm

theorem join_0_0 : (twinPrimeSegment 57016365 57081901).card = 250 := by
  simpa using combineTwinPrimeSegments (by decide : 57016365 ≤ 57049133)
    (by decide : 57049133 ≤ 57081901) block0 block1

theorem join_0_1 : (twinPrimeSegment 57081901 57147437).card = 290 := by
  simpa using combineTwinPrimeSegments (by decide : 57081901 ≤ 57114669)
    (by decide : 57114669 ≤ 57147437) block2 block3

theorem join_1_0 : (twinPrimeSegment 57016365 57147437).card = 540 := by
  simpa using combineTwinPrimeSegments (by decide : 57016365 ≤ 57081901)
    (by decide : 57081901 ≤ 57147437) join_0_0 join_0_1

theorem total : (twinPrimeSegment 57016365 57147437).card = 540 := join_1_0

end S027C03
end Sude.GeneratedTwinScan
