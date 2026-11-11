import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinGeometricScan

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S019C08
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def widths0 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked0 : geometricActiveStreamingTwinScan finiteTwinCheckedBase 40894509 widths0 = 126 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 40894509 40927277).card = 126 := by
  have h := geometricActiveStreamingTwinScan_spec finiteTwinCheckedBase 32768 40894509 widths0
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [checked0] at h
  simpa [widths0] using h.symm

def widths1 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked1 : geometricActiveStreamingTwinScan finiteTwinCheckedBase 40927277 widths1 = 137 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 40927277 40960045).card = 137 := by
  have h := geometricActiveStreamingTwinScan_spec finiteTwinCheckedBase 32768 40927277 widths1
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [checked1] at h
  simpa [widths1] using h.symm

def widths2 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked2 : geometricActiveStreamingTwinScan finiteTwinCheckedBase 40960045 widths2 = 141 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 40960045 40992813).card = 141 := by
  have h := geometricActiveStreamingTwinScan_spec finiteTwinCheckedBase 32768 40960045 widths2
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [checked2] at h
  simpa [widths2] using h.symm

def widths3 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked3 : geometricActiveStreamingTwinScan finiteTwinCheckedBase 40992813 widths3 = 130 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 40992813 41025581).card = 130 := by
  have h := geometricActiveStreamingTwinScan_spec finiteTwinCheckedBase 32768 40992813 widths3
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [checked3] at h
  simpa [widths3] using h.symm

theorem join_0_0 : (twinPrimeSegment 40894509 40960045).card = 263 := by
  simpa using combineTwinPrimeSegments (by decide : 40894509 ≤ 40927277)
    (by decide : 40927277 ≤ 40960045) block0 block1

theorem join_0_1 : (twinPrimeSegment 40960045 41025581).card = 271 := by
  simpa using combineTwinPrimeSegments (by decide : 40960045 ≤ 40992813)
    (by decide : 40992813 ≤ 41025581) block2 block3

theorem join_1_0 : (twinPrimeSegment 40894509 41025581).card = 534 := by
  simpa using combineTwinPrimeSegments (by decide : 40894509 ≤ 40960045)
    (by decide : 40960045 ≤ 41025581) join_0_0 join_0_1

theorem total : (twinPrimeSegment 40894509 41025581).card = 534 := join_1_0

end S019C08
end Sude.GeneratedTwinScan
