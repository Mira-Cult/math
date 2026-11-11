import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinGeometricScan

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S017C05
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def widths0 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked0 : geometricActiveStreamingTwinScan finiteTwinCheckedBase 36306989 widths0 = 143 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 36306989 36339757).card = 143 := by
  have h := geometricActiveStreamingTwinScan_spec finiteTwinCheckedBase 32768 36306989 widths0
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [checked0] at h
  simpa [widths0] using h.symm

def widths1 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked1 : geometricActiveStreamingTwinScan finiteTwinCheckedBase 36339757 widths1 = 160 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 36339757 36372525).card = 160 := by
  have h := geometricActiveStreamingTwinScan_spec finiteTwinCheckedBase 32768 36339757 widths1
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [checked1] at h
  simpa [widths1] using h.symm

def widths2 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked2 : geometricActiveStreamingTwinScan finiteTwinCheckedBase 36372525 widths2 = 141 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 36372525 36405293).card = 141 := by
  have h := geometricActiveStreamingTwinScan_spec finiteTwinCheckedBase 32768 36372525 widths2
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [checked2] at h
  simpa [widths2] using h.symm

def widths3 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked3 : geometricActiveStreamingTwinScan finiteTwinCheckedBase 36405293 widths3 = 136 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 36405293 36438061).card = 136 := by
  have h := geometricActiveStreamingTwinScan_spec finiteTwinCheckedBase 32768 36405293 widths3
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [checked3] at h
  simpa [widths3] using h.symm

theorem join_0_0 : (twinPrimeSegment 36306989 36372525).card = 303 := by
  simpa using combineTwinPrimeSegments (by decide : 36306989 ≤ 36339757)
    (by decide : 36339757 ≤ 36372525) block0 block1

theorem join_0_1 : (twinPrimeSegment 36372525 36438061).card = 277 := by
  simpa using combineTwinPrimeSegments (by decide : 36372525 ≤ 36405293)
    (by decide : 36405293 ≤ 36438061) block2 block3

theorem join_1_0 : (twinPrimeSegment 36306989 36438061).card = 580 := by
  simpa using combineTwinPrimeSegments (by decide : 36306989 ≤ 36372525)
    (by decide : 36372525 ≤ 36438061) join_0_0 join_0_1

theorem total : (twinPrimeSegment 36306989 36438061).card = 580 := join_1_0

end S017C05
end Sude.GeneratedTwinScan
