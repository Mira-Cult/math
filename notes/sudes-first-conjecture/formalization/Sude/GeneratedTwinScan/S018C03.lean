import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinGeometricScan

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S018C03
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def widths0 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked0 : geometricActiveStreamingTwinScan finiteTwinCheckedBase 38141997 widths0 = 160 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 38141997 38174765).card = 160 := by
  have h := geometricActiveStreamingTwinScan_spec finiteTwinCheckedBase 32768 38141997 widths0
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [checked0] at h
  simpa [widths0] using h.symm

def widths1 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked1 : geometricActiveStreamingTwinScan finiteTwinCheckedBase 38174765 widths1 = 151 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 38174765 38207533).card = 151 := by
  have h := geometricActiveStreamingTwinScan_spec finiteTwinCheckedBase 32768 38174765 widths1
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [checked1] at h
  simpa [widths1] using h.symm

def widths2 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked2 : geometricActiveStreamingTwinScan finiteTwinCheckedBase 38207533 widths2 = 144 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 38207533 38240301).card = 144 := by
  have h := geometricActiveStreamingTwinScan_spec finiteTwinCheckedBase 32768 38207533 widths2
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [checked2] at h
  simpa [widths2] using h.symm

def widths3 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked3 : geometricActiveStreamingTwinScan finiteTwinCheckedBase 38240301 widths3 = 137 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 38240301 38273069).card = 137 := by
  have h := geometricActiveStreamingTwinScan_spec finiteTwinCheckedBase 32768 38240301 widths3
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [checked3] at h
  simpa [widths3] using h.symm

theorem join_0_0 : (twinPrimeSegment 38141997 38207533).card = 311 := by
  simpa using combineTwinPrimeSegments (by decide : 38141997 ≤ 38174765)
    (by decide : 38174765 ≤ 38207533) block0 block1

theorem join_0_1 : (twinPrimeSegment 38207533 38273069).card = 281 := by
  simpa using combineTwinPrimeSegments (by decide : 38207533 ≤ 38240301)
    (by decide : 38240301 ≤ 38273069) block2 block3

theorem join_1_0 : (twinPrimeSegment 38141997 38273069).card = 592 := by
  simpa using combineTwinPrimeSegments (by decide : 38141997 ≤ 38207533)
    (by decide : 38207533 ≤ 38273069) join_0_0 join_0_1

theorem total : (twinPrimeSegment 38141997 38273069).card = 592 := join_1_0

end S018C03
end Sude.GeneratedTwinScan
