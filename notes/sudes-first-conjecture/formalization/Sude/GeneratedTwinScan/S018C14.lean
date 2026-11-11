import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinGeometricScan

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S018C14
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def widths0 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked0 : geometricActiveStreamingTwinScan finiteTwinCheckedBase 39583789 widths0 = 143 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 39583789 39616557).card = 143 := by
  have h := geometricActiveStreamingTwinScan_spec finiteTwinCheckedBase 32768 39583789 widths0
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [checked0] at h
  simpa [widths0] using h.symm

def widths1 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked1 : geometricActiveStreamingTwinScan finiteTwinCheckedBase 39616557 widths1 = 165 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 39616557 39649325).card = 165 := by
  have h := geometricActiveStreamingTwinScan_spec finiteTwinCheckedBase 32768 39616557 widths1
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [checked1] at h
  simpa [widths1] using h.symm

def widths2 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked2 : geometricActiveStreamingTwinScan finiteTwinCheckedBase 39649325 widths2 = 137 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 39649325 39682093).card = 137 := by
  have h := geometricActiveStreamingTwinScan_spec finiteTwinCheckedBase 32768 39649325 widths2
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [checked2] at h
  simpa [widths2] using h.symm

def widths3 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked3 : geometricActiveStreamingTwinScan finiteTwinCheckedBase 39682093 widths3 = 138 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 39682093 39714861).card = 138 := by
  have h := geometricActiveStreamingTwinScan_spec finiteTwinCheckedBase 32768 39682093 widths3
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [checked3] at h
  simpa [widths3] using h.symm

theorem join_0_0 : (twinPrimeSegment 39583789 39649325).card = 308 := by
  simpa using combineTwinPrimeSegments (by decide : 39583789 ≤ 39616557)
    (by decide : 39616557 ≤ 39649325) block0 block1

theorem join_0_1 : (twinPrimeSegment 39649325 39714861).card = 275 := by
  simpa using combineTwinPrimeSegments (by decide : 39649325 ≤ 39682093)
    (by decide : 39682093 ≤ 39714861) block2 block3

theorem join_1_0 : (twinPrimeSegment 39583789 39714861).card = 583 := by
  simpa using combineTwinPrimeSegments (by decide : 39583789 ≤ 39649325)
    (by decide : 39649325 ≤ 39714861) join_0_0 join_0_1

theorem total : (twinPrimeSegment 39583789 39714861).card = 583 := join_1_0

end S018C14
end Sude.GeneratedTwinScan
