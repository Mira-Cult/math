import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinGeometricScan

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S018C05
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def widths0 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked0 : geometricActiveStreamingTwinScan finiteTwinCheckedBase 38404141 widths0 = 134 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 38404141 38436909).card = 134 := by
  have h := geometricActiveStreamingTwinScan_spec finiteTwinCheckedBase 32768 38404141 widths0
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [checked0] at h
  simpa [widths0] using h.symm

def widths1 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked1 : geometricActiveStreamingTwinScan finiteTwinCheckedBase 38436909 widths1 = 137 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 38436909 38469677).card = 137 := by
  have h := geometricActiveStreamingTwinScan_spec finiteTwinCheckedBase 32768 38436909 widths1
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [checked1] at h
  simpa [widths1] using h.symm

def widths2 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked2 : geometricActiveStreamingTwinScan finiteTwinCheckedBase 38469677 widths2 = 136 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 38469677 38502445).card = 136 := by
  have h := geometricActiveStreamingTwinScan_spec finiteTwinCheckedBase 32768 38469677 widths2
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [checked2] at h
  simpa [widths2] using h.symm

def widths3 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked3 : geometricActiveStreamingTwinScan finiteTwinCheckedBase 38502445 widths3 = 138 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 38502445 38535213).card = 138 := by
  have h := geometricActiveStreamingTwinScan_spec finiteTwinCheckedBase 32768 38502445 widths3
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [checked3] at h
  simpa [widths3] using h.symm

theorem join_0_0 : (twinPrimeSegment 38404141 38469677).card = 271 := by
  simpa using combineTwinPrimeSegments (by decide : 38404141 ≤ 38436909)
    (by decide : 38436909 ≤ 38469677) block0 block1

theorem join_0_1 : (twinPrimeSegment 38469677 38535213).card = 274 := by
  simpa using combineTwinPrimeSegments (by decide : 38469677 ≤ 38502445)
    (by decide : 38502445 ≤ 38535213) block2 block3

theorem join_1_0 : (twinPrimeSegment 38404141 38535213).card = 545 := by
  simpa using combineTwinPrimeSegments (by decide : 38404141 ≤ 38469677)
    (by decide : 38469677 ≤ 38535213) join_0_0 join_0_1

theorem total : (twinPrimeSegment 38404141 38535213).card = 545 := join_1_0

end S018C05
end Sude.GeneratedTwinScan
