import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinGeometricScan

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S027C11
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def widths0 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked0 : geometricActiveStreamingTwinScan finiteTwinCheckedBase 58064941 widths0 = 143 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 58064941 58097709).card = 143 := by
  have h := geometricActiveStreamingTwinScan_spec finiteTwinCheckedBase 32768 58064941 widths0
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [checked0] at h
  simpa [widths0] using h.symm

def widths1 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked1 : geometricActiveStreamingTwinScan finiteTwinCheckedBase 58097709 widths1 = 128 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 58097709 58130477).card = 128 := by
  have h := geometricActiveStreamingTwinScan_spec finiteTwinCheckedBase 32768 58097709 widths1
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [checked1] at h
  simpa [widths1] using h.symm

def widths2 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked2 : geometricActiveStreamingTwinScan finiteTwinCheckedBase 58130477 widths2 = 141 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 58130477 58163245).card = 141 := by
  have h := geometricActiveStreamingTwinScan_spec finiteTwinCheckedBase 32768 58130477 widths2
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [checked2] at h
  simpa [widths2] using h.symm

def widths3 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked3 : geometricActiveStreamingTwinScan finiteTwinCheckedBase 58163245 widths3 = 126 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 58163245 58196013).card = 126 := by
  have h := geometricActiveStreamingTwinScan_spec finiteTwinCheckedBase 32768 58163245 widths3
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [checked3] at h
  simpa [widths3] using h.symm

theorem join_0_0 : (twinPrimeSegment 58064941 58130477).card = 271 := by
  simpa using combineTwinPrimeSegments (by decide : 58064941 ≤ 58097709)
    (by decide : 58097709 ≤ 58130477) block0 block1

theorem join_0_1 : (twinPrimeSegment 58130477 58196013).card = 267 := by
  simpa using combineTwinPrimeSegments (by decide : 58130477 ≤ 58163245)
    (by decide : 58163245 ≤ 58196013) block2 block3

theorem join_1_0 : (twinPrimeSegment 58064941 58196013).card = 538 := by
  simpa using combineTwinPrimeSegments (by decide : 58064941 ≤ 58130477)
    (by decide : 58130477 ≤ 58196013) join_0_0 join_0_1

theorem total : (twinPrimeSegment 58064941 58196013).card = 538 := join_1_0

end S027C11
end Sude.GeneratedTwinScan
