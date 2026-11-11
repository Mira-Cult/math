import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinGeometricScan

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S016C00
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def widths0 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked0 : geometricActiveStreamingTwinScan finiteTwinCheckedBase 33554477 widths0 = 139 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 33554477 33587245).card = 139 := by
  have h := geometricActiveStreamingTwinScan_spec finiteTwinCheckedBase 32768 33554477 widths0
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [checked0] at h
  simpa [widths0] using h.symm

def widths1 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked1 : geometricActiveStreamingTwinScan finiteTwinCheckedBase 33587245 widths1 = 164 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 33587245 33620013).card = 164 := by
  have h := geometricActiveStreamingTwinScan_spec finiteTwinCheckedBase 32768 33587245 widths1
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [checked1] at h
  simpa [widths1] using h.symm

def widths2 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked2 : geometricActiveStreamingTwinScan finiteTwinCheckedBase 33620013 widths2 = 147 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 33620013 33652781).card = 147 := by
  have h := geometricActiveStreamingTwinScan_spec finiteTwinCheckedBase 32768 33620013 widths2
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [checked2] at h
  simpa [widths2] using h.symm

def widths3 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked3 : geometricActiveStreamingTwinScan finiteTwinCheckedBase 33652781 widths3 = 155 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 33652781 33685549).card = 155 := by
  have h := geometricActiveStreamingTwinScan_spec finiteTwinCheckedBase 32768 33652781 widths3
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [checked3] at h
  simpa [widths3] using h.symm

theorem join_0_0 : (twinPrimeSegment 33554477 33620013).card = 303 := by
  simpa using combineTwinPrimeSegments (by decide : 33554477 ≤ 33587245)
    (by decide : 33587245 ≤ 33620013) block0 block1

theorem join_0_1 : (twinPrimeSegment 33620013 33685549).card = 302 := by
  simpa using combineTwinPrimeSegments (by decide : 33620013 ≤ 33652781)
    (by decide : 33652781 ≤ 33685549) block2 block3

theorem join_1_0 : (twinPrimeSegment 33554477 33685549).card = 605 := by
  simpa using combineTwinPrimeSegments (by decide : 33554477 ≤ 33620013)
    (by decide : 33620013 ≤ 33685549) join_0_0 join_0_1

theorem total : (twinPrimeSegment 33554477 33685549).card = 605 := join_1_0

end S016C00
end Sude.GeneratedTwinScan
