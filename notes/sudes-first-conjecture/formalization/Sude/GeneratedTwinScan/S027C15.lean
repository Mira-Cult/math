import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinGeometricScan

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S027C15
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def widths0 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked0 : geometricActiveStreamingTwinScan finiteTwinCheckedBase 58589229 widths0 = 136 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 58589229 58621997).card = 136 := by
  have h := geometricActiveStreamingTwinScan_spec finiteTwinCheckedBase 32768 58589229 widths0
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [checked0] at h
  simpa [widths0] using h.symm

def widths1 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked1 : geometricActiveStreamingTwinScan finiteTwinCheckedBase 58621997 widths1 = 137 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 58621997 58654765).card = 137 := by
  have h := geometricActiveStreamingTwinScan_spec finiteTwinCheckedBase 32768 58621997 widths1
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [checked1] at h
  simpa [widths1] using h.symm

def widths2 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked2 : geometricActiveStreamingTwinScan finiteTwinCheckedBase 58654765 widths2 = 138 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 58654765 58687533).card = 138 := by
  have h := geometricActiveStreamingTwinScan_spec finiteTwinCheckedBase 32768 58654765 widths2
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [checked2] at h
  simpa [widths2] using h.symm

def widths3 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked3 : geometricActiveStreamingTwinScan finiteTwinCheckedBase 58687533 widths3 = 142 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 58687533 58720301).card = 142 := by
  have h := geometricActiveStreamingTwinScan_spec finiteTwinCheckedBase 32768 58687533 widths3
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [checked3] at h
  simpa [widths3] using h.symm

theorem join_0_0 : (twinPrimeSegment 58589229 58654765).card = 273 := by
  simpa using combineTwinPrimeSegments (by decide : 58589229 ≤ 58621997)
    (by decide : 58621997 ≤ 58654765) block0 block1

theorem join_0_1 : (twinPrimeSegment 58654765 58720301).card = 280 := by
  simpa using combineTwinPrimeSegments (by decide : 58654765 ≤ 58687533)
    (by decide : 58687533 ≤ 58720301) block2 block3

theorem join_1_0 : (twinPrimeSegment 58589229 58720301).card = 553 := by
  simpa using combineTwinPrimeSegments (by decide : 58589229 ≤ 58654765)
    (by decide : 58654765 ≤ 58720301) join_0_0 join_0_1

theorem total : (twinPrimeSegment 58589229 58720301).card = 553 := join_1_0

end S027C15
end Sude.GeneratedTwinScan
