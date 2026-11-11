import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinGeometricScan

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S020C07
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def widths0 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked0 : geometricActiveStreamingTwinScan finiteTwinCheckedBase 42860589 widths0 = 132 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 42860589 42893357).card = 132 := by
  have h := geometricActiveStreamingTwinScan_spec finiteTwinCheckedBase 32768 42860589 widths0
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [checked0] at h
  simpa [widths0] using h.symm

def widths1 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked1 : geometricActiveStreamingTwinScan finiteTwinCheckedBase 42893357 widths1 = 144 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 42893357 42926125).card = 144 := by
  have h := geometricActiveStreamingTwinScan_spec finiteTwinCheckedBase 32768 42893357 widths1
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [checked1] at h
  simpa [widths1] using h.symm

def widths2 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked2 : geometricActiveStreamingTwinScan finiteTwinCheckedBase 42926125 widths2 = 136 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 42926125 42958893).card = 136 := by
  have h := geometricActiveStreamingTwinScan_spec finiteTwinCheckedBase 32768 42926125 widths2
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [checked2] at h
  simpa [widths2] using h.symm

def widths3 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked3 : geometricActiveStreamingTwinScan finiteTwinCheckedBase 42958893 widths3 = 130 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 42958893 42991661).card = 130 := by
  have h := geometricActiveStreamingTwinScan_spec finiteTwinCheckedBase 32768 42958893 widths3
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [checked3] at h
  simpa [widths3] using h.symm

theorem join_0_0 : (twinPrimeSegment 42860589 42926125).card = 276 := by
  simpa using combineTwinPrimeSegments (by decide : 42860589 ≤ 42893357)
    (by decide : 42893357 ≤ 42926125) block0 block1

theorem join_0_1 : (twinPrimeSegment 42926125 42991661).card = 266 := by
  simpa using combineTwinPrimeSegments (by decide : 42926125 ≤ 42958893)
    (by decide : 42958893 ≤ 42991661) block2 block3

theorem join_1_0 : (twinPrimeSegment 42860589 42991661).card = 542 := by
  simpa using combineTwinPrimeSegments (by decide : 42860589 ≤ 42926125)
    (by decide : 42926125 ≤ 42991661) join_0_0 join_0_1

theorem total : (twinPrimeSegment 42860589 42991661).card = 542 := join_1_0

end S020C07
end Sude.GeneratedTwinScan
