import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinGeometricScan

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S017C12
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def widths0 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked0 : geometricActiveStreamingTwinScan finiteTwinCheckedBase 37224493 widths0 = 140 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 37224493 37257261).card = 140 := by
  have h := geometricActiveStreamingTwinScan_spec finiteTwinCheckedBase 32768 37224493 widths0
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [checked0] at h
  simpa [widths0] using h.symm

def widths1 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked1 : geometricActiveStreamingTwinScan finiteTwinCheckedBase 37257261 widths1 = 139 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 37257261 37290029).card = 139 := by
  have h := geometricActiveStreamingTwinScan_spec finiteTwinCheckedBase 32768 37257261 widths1
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [checked1] at h
  simpa [widths1] using h.symm

def widths2 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked2 : geometricActiveStreamingTwinScan finiteTwinCheckedBase 37290029 widths2 = 131 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 37290029 37322797).card = 131 := by
  have h := geometricActiveStreamingTwinScan_spec finiteTwinCheckedBase 32768 37290029 widths2
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [checked2] at h
  simpa [widths2] using h.symm

def widths3 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked3 : geometricActiveStreamingTwinScan finiteTwinCheckedBase 37322797 widths3 = 145 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 37322797 37355565).card = 145 := by
  have h := geometricActiveStreamingTwinScan_spec finiteTwinCheckedBase 32768 37322797 widths3
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [checked3] at h
  simpa [widths3] using h.symm

theorem join_0_0 : (twinPrimeSegment 37224493 37290029).card = 279 := by
  simpa using combineTwinPrimeSegments (by decide : 37224493 ≤ 37257261)
    (by decide : 37257261 ≤ 37290029) block0 block1

theorem join_0_1 : (twinPrimeSegment 37290029 37355565).card = 276 := by
  simpa using combineTwinPrimeSegments (by decide : 37290029 ≤ 37322797)
    (by decide : 37322797 ≤ 37355565) block2 block3

theorem join_1_0 : (twinPrimeSegment 37224493 37355565).card = 555 := by
  simpa using combineTwinPrimeSegments (by decide : 37224493 ≤ 37290029)
    (by decide : 37290029 ≤ 37355565) join_0_0 join_0_1

theorem total : (twinPrimeSegment 37224493 37355565).card = 555 := join_1_0

end S017C12
end Sude.GeneratedTwinScan
