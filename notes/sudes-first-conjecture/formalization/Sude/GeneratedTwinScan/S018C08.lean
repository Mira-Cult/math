import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinGeometricScan

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S018C08
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def widths0 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked0 : geometricActiveStreamingTwinScan finiteTwinCheckedBase 38797357 widths0 = 123 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 38797357 38830125).card = 123 := by
  have h := geometricActiveStreamingTwinScan_spec finiteTwinCheckedBase 32768 38797357 widths0
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [checked0] at h
  simpa [widths0] using h.symm

def widths1 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked1 : geometricActiveStreamingTwinScan finiteTwinCheckedBase 38830125 widths1 = 148 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 38830125 38862893).card = 148 := by
  have h := geometricActiveStreamingTwinScan_spec finiteTwinCheckedBase 32768 38830125 widths1
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [checked1] at h
  simpa [widths1] using h.symm

def widths2 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked2 : geometricActiveStreamingTwinScan finiteTwinCheckedBase 38862893 widths2 = 138 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 38862893 38895661).card = 138 := by
  have h := geometricActiveStreamingTwinScan_spec finiteTwinCheckedBase 32768 38862893 widths2
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [checked2] at h
  simpa [widths2] using h.symm

def widths3 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked3 : geometricActiveStreamingTwinScan finiteTwinCheckedBase 38895661 widths3 = 149 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 38895661 38928429).card = 149 := by
  have h := geometricActiveStreamingTwinScan_spec finiteTwinCheckedBase 32768 38895661 widths3
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [checked3] at h
  simpa [widths3] using h.symm

theorem join_0_0 : (twinPrimeSegment 38797357 38862893).card = 271 := by
  simpa using combineTwinPrimeSegments (by decide : 38797357 ≤ 38830125)
    (by decide : 38830125 ≤ 38862893) block0 block1

theorem join_0_1 : (twinPrimeSegment 38862893 38928429).card = 287 := by
  simpa using combineTwinPrimeSegments (by decide : 38862893 ≤ 38895661)
    (by decide : 38895661 ≤ 38928429) block2 block3

theorem join_1_0 : (twinPrimeSegment 38797357 38928429).card = 558 := by
  simpa using combineTwinPrimeSegments (by decide : 38797357 ≤ 38862893)
    (by decide : 38862893 ≤ 38928429) join_0_0 join_0_1

theorem total : (twinPrimeSegment 38797357 38928429).card = 558 := join_1_0

end S018C08
end Sude.GeneratedTwinScan
