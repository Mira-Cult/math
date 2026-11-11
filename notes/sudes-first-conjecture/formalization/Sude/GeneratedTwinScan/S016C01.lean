import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinGeometricScan

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S016C01
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def widths0 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked0 : geometricActiveStreamingTwinScan finiteTwinCheckedBase 33685549 widths0 = 148 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 33685549 33718317).card = 148 := by
  have h := geometricActiveStreamingTwinScan_spec finiteTwinCheckedBase 32768 33685549 widths0
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [checked0] at h
  simpa [widths0] using h.symm

def widths1 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked1 : geometricActiveStreamingTwinScan finiteTwinCheckedBase 33718317 widths1 = 128 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 33718317 33751085).card = 128 := by
  have h := geometricActiveStreamingTwinScan_spec finiteTwinCheckedBase 32768 33718317 widths1
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [checked1] at h
  simpa [widths1] using h.symm

def widths2 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked2 : geometricActiveStreamingTwinScan finiteTwinCheckedBase 33751085 widths2 = 124 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 33751085 33783853).card = 124 := by
  have h := geometricActiveStreamingTwinScan_spec finiteTwinCheckedBase 32768 33751085 widths2
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [checked2] at h
  simpa [widths2] using h.symm

def widths3 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked3 : geometricActiveStreamingTwinScan finiteTwinCheckedBase 33783853 widths3 = 143 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 33783853 33816621).card = 143 := by
  have h := geometricActiveStreamingTwinScan_spec finiteTwinCheckedBase 32768 33783853 widths3
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [checked3] at h
  simpa [widths3] using h.symm

theorem join_0_0 : (twinPrimeSegment 33685549 33751085).card = 276 := by
  simpa using combineTwinPrimeSegments (by decide : 33685549 ≤ 33718317)
    (by decide : 33718317 ≤ 33751085) block0 block1

theorem join_0_1 : (twinPrimeSegment 33751085 33816621).card = 267 := by
  simpa using combineTwinPrimeSegments (by decide : 33751085 ≤ 33783853)
    (by decide : 33783853 ≤ 33816621) block2 block3

theorem join_1_0 : (twinPrimeSegment 33685549 33816621).card = 543 := by
  simpa using combineTwinPrimeSegments (by decide : 33685549 ≤ 33751085)
    (by decide : 33751085 ≤ 33816621) join_0_0 join_0_1

theorem total : (twinPrimeSegment 33685549 33816621).card = 543 := join_1_0

end S016C01
end Sude.GeneratedTwinScan
