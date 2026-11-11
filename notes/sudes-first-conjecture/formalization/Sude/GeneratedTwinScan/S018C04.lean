import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinGeometricScan

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S018C04
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def widths0 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked0 : geometricActiveStreamingTwinScan finiteTwinCheckedBase 38273069 widths0 = 167 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 38273069 38305837).card = 167 := by
  have h := geometricActiveStreamingTwinScan_spec finiteTwinCheckedBase 32768 38273069 widths0
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [checked0] at h
  simpa [widths0] using h.symm

def widths1 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked1 : geometricActiveStreamingTwinScan finiteTwinCheckedBase 38305837 widths1 = 132 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 38305837 38338605).card = 132 := by
  have h := geometricActiveStreamingTwinScan_spec finiteTwinCheckedBase 32768 38305837 widths1
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [checked1] at h
  simpa [widths1] using h.symm

def widths2 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked2 : geometricActiveStreamingTwinScan finiteTwinCheckedBase 38338605 widths2 = 133 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 38338605 38371373).card = 133 := by
  have h := geometricActiveStreamingTwinScan_spec finiteTwinCheckedBase 32768 38338605 widths2
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [checked2] at h
  simpa [widths2] using h.symm

def widths3 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked3 : geometricActiveStreamingTwinScan finiteTwinCheckedBase 38371373 widths3 = 124 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 38371373 38404141).card = 124 := by
  have h := geometricActiveStreamingTwinScan_spec finiteTwinCheckedBase 32768 38371373 widths3
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [checked3] at h
  simpa [widths3] using h.symm

theorem join_0_0 : (twinPrimeSegment 38273069 38338605).card = 299 := by
  simpa using combineTwinPrimeSegments (by decide : 38273069 ≤ 38305837)
    (by decide : 38305837 ≤ 38338605) block0 block1

theorem join_0_1 : (twinPrimeSegment 38338605 38404141).card = 257 := by
  simpa using combineTwinPrimeSegments (by decide : 38338605 ≤ 38371373)
    (by decide : 38371373 ≤ 38404141) block2 block3

theorem join_1_0 : (twinPrimeSegment 38273069 38404141).card = 556 := by
  simpa using combineTwinPrimeSegments (by decide : 38273069 ≤ 38338605)
    (by decide : 38338605 ≤ 38404141) join_0_0 join_0_1

theorem total : (twinPrimeSegment 38273069 38404141).card = 556 := join_1_0

end S018C04
end Sude.GeneratedTwinScan
