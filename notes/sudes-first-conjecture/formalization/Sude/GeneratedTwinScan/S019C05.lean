import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinGeometricScan

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S019C05
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def widths0 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked0 : geometricActiveStreamingTwinScan finiteTwinCheckedBase 40501293 widths0 = 126 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 40501293 40534061).card = 126 := by
  have h := geometricActiveStreamingTwinScan_spec finiteTwinCheckedBase 32768 40501293 widths0
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [checked0] at h
  simpa [widths0] using h.symm

def widths1 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked1 : geometricActiveStreamingTwinScan finiteTwinCheckedBase 40534061 widths1 = 139 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 40534061 40566829).card = 139 := by
  have h := geometricActiveStreamingTwinScan_spec finiteTwinCheckedBase 32768 40534061 widths1
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [checked1] at h
  simpa [widths1] using h.symm

def widths2 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked2 : geometricActiveStreamingTwinScan finiteTwinCheckedBase 40566829 widths2 = 133 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 40566829 40599597).card = 133 := by
  have h := geometricActiveStreamingTwinScan_spec finiteTwinCheckedBase 32768 40566829 widths2
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [checked2] at h
  simpa [widths2] using h.symm

def widths3 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked3 : geometricActiveStreamingTwinScan finiteTwinCheckedBase 40599597 widths3 = 147 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 40599597 40632365).card = 147 := by
  have h := geometricActiveStreamingTwinScan_spec finiteTwinCheckedBase 32768 40599597 widths3
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [checked3] at h
  simpa [widths3] using h.symm

theorem join_0_0 : (twinPrimeSegment 40501293 40566829).card = 265 := by
  simpa using combineTwinPrimeSegments (by decide : 40501293 ≤ 40534061)
    (by decide : 40534061 ≤ 40566829) block0 block1

theorem join_0_1 : (twinPrimeSegment 40566829 40632365).card = 280 := by
  simpa using combineTwinPrimeSegments (by decide : 40566829 ≤ 40599597)
    (by decide : 40599597 ≤ 40632365) block2 block3

theorem join_1_0 : (twinPrimeSegment 40501293 40632365).card = 545 := by
  simpa using combineTwinPrimeSegments (by decide : 40501293 ≤ 40566829)
    (by decide : 40566829 ≤ 40632365) join_0_0 join_0_1

theorem total : (twinPrimeSegment 40501293 40632365).card = 545 := join_1_0

end S019C05
end Sude.GeneratedTwinScan
