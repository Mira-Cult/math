import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinGeometricScan

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S027C02
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def widths0 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked0 : geometricActiveStreamingTwinScan finiteTwinCheckedBase 56885293 widths0 = 151 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 56885293 56918061).card = 151 := by
  have h := geometricActiveStreamingTwinScan_spec finiteTwinCheckedBase 32768 56885293 widths0
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [checked0] at h
  simpa [widths0] using h.symm

def widths1 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked1 : geometricActiveStreamingTwinScan finiteTwinCheckedBase 56918061 widths1 = 154 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 56918061 56950829).card = 154 := by
  have h := geometricActiveStreamingTwinScan_spec finiteTwinCheckedBase 32768 56918061 widths1
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [checked1] at h
  simpa [widths1] using h.symm

def widths2 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked2 : geometricActiveStreamingTwinScan finiteTwinCheckedBase 56950829 widths2 = 129 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 56950829 56983597).card = 129 := by
  have h := geometricActiveStreamingTwinScan_spec finiteTwinCheckedBase 32768 56950829 widths2
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [checked2] at h
  simpa [widths2] using h.symm

def widths3 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked3 : geometricActiveStreamingTwinScan finiteTwinCheckedBase 56983597 widths3 = 142 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 56983597 57016365).card = 142 := by
  have h := geometricActiveStreamingTwinScan_spec finiteTwinCheckedBase 32768 56983597 widths3
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [checked3] at h
  simpa [widths3] using h.symm

theorem join_0_0 : (twinPrimeSegment 56885293 56950829).card = 305 := by
  simpa using combineTwinPrimeSegments (by decide : 56885293 ≤ 56918061)
    (by decide : 56918061 ≤ 56950829) block0 block1

theorem join_0_1 : (twinPrimeSegment 56950829 57016365).card = 271 := by
  simpa using combineTwinPrimeSegments (by decide : 56950829 ≤ 56983597)
    (by decide : 56983597 ≤ 57016365) block2 block3

theorem join_1_0 : (twinPrimeSegment 56885293 57016365).card = 576 := by
  simpa using combineTwinPrimeSegments (by decide : 56885293 ≤ 56950829)
    (by decide : 56950829 ≤ 57016365) join_0_0 join_0_1

theorem total : (twinPrimeSegment 56885293 57016365).card = 576 := join_1_0

end S027C02
end Sude.GeneratedTwinScan
