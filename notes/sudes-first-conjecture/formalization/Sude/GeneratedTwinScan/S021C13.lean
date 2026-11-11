import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinGeometricScan

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S021C13
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def widths0 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked0 : geometricActiveStreamingTwinScan finiteTwinCheckedBase 45744173 widths0 = 135 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 45744173 45776941).card = 135 := by
  have h := geometricActiveStreamingTwinScan_spec finiteTwinCheckedBase 32768 45744173 widths0
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [checked0] at h
  simpa [widths0] using h.symm

def widths1 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked1 : geometricActiveStreamingTwinScan finiteTwinCheckedBase 45776941 widths1 = 146 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 45776941 45809709).card = 146 := by
  have h := geometricActiveStreamingTwinScan_spec finiteTwinCheckedBase 32768 45776941 widths1
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [checked1] at h
  simpa [widths1] using h.symm

def widths2 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked2 : geometricActiveStreamingTwinScan finiteTwinCheckedBase 45809709 widths2 = 136 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 45809709 45842477).card = 136 := by
  have h := geometricActiveStreamingTwinScan_spec finiteTwinCheckedBase 32768 45809709 widths2
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [checked2] at h
  simpa [widths2] using h.symm

def widths3 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked3 : geometricActiveStreamingTwinScan finiteTwinCheckedBase 45842477 widths3 = 130 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 45842477 45875245).card = 130 := by
  have h := geometricActiveStreamingTwinScan_spec finiteTwinCheckedBase 32768 45842477 widths3
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [checked3] at h
  simpa [widths3] using h.symm

theorem join_0_0 : (twinPrimeSegment 45744173 45809709).card = 281 := by
  simpa using combineTwinPrimeSegments (by decide : 45744173 ≤ 45776941)
    (by decide : 45776941 ≤ 45809709) block0 block1

theorem join_0_1 : (twinPrimeSegment 45809709 45875245).card = 266 := by
  simpa using combineTwinPrimeSegments (by decide : 45809709 ≤ 45842477)
    (by decide : 45842477 ≤ 45875245) block2 block3

theorem join_1_0 : (twinPrimeSegment 45744173 45875245).card = 547 := by
  simpa using combineTwinPrimeSegments (by decide : 45744173 ≤ 45809709)
    (by decide : 45809709 ≤ 45875245) join_0_0 join_0_1

theorem total : (twinPrimeSegment 45744173 45875245).card = 547 := join_1_0

end S021C13
end Sude.GeneratedTwinScan
