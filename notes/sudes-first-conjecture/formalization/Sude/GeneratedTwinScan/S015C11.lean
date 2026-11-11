import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinGeometricScan

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S015C11
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def widths0 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked0 : geometricActiveStreamingTwinScan finiteTwinCheckedBase 32899117 widths0 = 152 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 32899117 32931885).card = 152 := by
  have h := geometricActiveStreamingTwinScan_spec finiteTwinCheckedBase 32768 32899117 widths0
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [checked0] at h
  simpa [widths0] using h.symm

def widths1 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked1 : geometricActiveStreamingTwinScan finiteTwinCheckedBase 32931885 widths1 = 155 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 32931885 32964653).card = 155 := by
  have h := geometricActiveStreamingTwinScan_spec finiteTwinCheckedBase 32768 32931885 widths1
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [checked1] at h
  simpa [widths1] using h.symm

def widths2 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked2 : geometricActiveStreamingTwinScan finiteTwinCheckedBase 32964653 widths2 = 140 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 32964653 32997421).card = 140 := by
  have h := geometricActiveStreamingTwinScan_spec finiteTwinCheckedBase 32768 32964653 widths2
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [checked2] at h
  simpa [widths2] using h.symm

def widths3 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked3 : geometricActiveStreamingTwinScan finiteTwinCheckedBase 32997421 widths3 = 127 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 32997421 33030189).card = 127 := by
  have h := geometricActiveStreamingTwinScan_spec finiteTwinCheckedBase 32768 32997421 widths3
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [checked3] at h
  simpa [widths3] using h.symm

theorem join_0_0 : (twinPrimeSegment 32899117 32964653).card = 307 := by
  simpa using combineTwinPrimeSegments (by decide : 32899117 ≤ 32931885)
    (by decide : 32931885 ≤ 32964653) block0 block1

theorem join_0_1 : (twinPrimeSegment 32964653 33030189).card = 267 := by
  simpa using combineTwinPrimeSegments (by decide : 32964653 ≤ 32997421)
    (by decide : 32997421 ≤ 33030189) block2 block3

theorem join_1_0 : (twinPrimeSegment 32899117 33030189).card = 574 := by
  simpa using combineTwinPrimeSegments (by decide : 32899117 ≤ 32964653)
    (by decide : 32964653 ≤ 33030189) join_0_0 join_0_1

theorem total : (twinPrimeSegment 32899117 33030189).card = 574 := join_1_0

end S015C11
end Sude.GeneratedTwinScan
