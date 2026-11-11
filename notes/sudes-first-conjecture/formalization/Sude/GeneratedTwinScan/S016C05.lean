import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinGeometricScan

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S016C05
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def widths0 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked0 : geometricActiveStreamingTwinScan finiteTwinCheckedBase 34209837 widths0 = 151 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 34209837 34242605).card = 151 := by
  have h := geometricActiveStreamingTwinScan_spec finiteTwinCheckedBase 32768 34209837 widths0
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [checked0] at h
  simpa [widths0] using h.symm

def widths1 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked1 : geometricActiveStreamingTwinScan finiteTwinCheckedBase 34242605 widths1 = 125 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 34242605 34275373).card = 125 := by
  have h := geometricActiveStreamingTwinScan_spec finiteTwinCheckedBase 32768 34242605 widths1
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [checked1] at h
  simpa [widths1] using h.symm

def widths2 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked2 : geometricActiveStreamingTwinScan finiteTwinCheckedBase 34275373 widths2 = 138 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 34275373 34308141).card = 138 := by
  have h := geometricActiveStreamingTwinScan_spec finiteTwinCheckedBase 32768 34275373 widths2
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [checked2] at h
  simpa [widths2] using h.symm

def widths3 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked3 : geometricActiveStreamingTwinScan finiteTwinCheckedBase 34308141 widths3 = 130 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 34308141 34340909).card = 130 := by
  have h := geometricActiveStreamingTwinScan_spec finiteTwinCheckedBase 32768 34308141 widths3
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [checked3] at h
  simpa [widths3] using h.symm

theorem join_0_0 : (twinPrimeSegment 34209837 34275373).card = 276 := by
  simpa using combineTwinPrimeSegments (by decide : 34209837 ≤ 34242605)
    (by decide : 34242605 ≤ 34275373) block0 block1

theorem join_0_1 : (twinPrimeSegment 34275373 34340909).card = 268 := by
  simpa using combineTwinPrimeSegments (by decide : 34275373 ≤ 34308141)
    (by decide : 34308141 ≤ 34340909) block2 block3

theorem join_1_0 : (twinPrimeSegment 34209837 34340909).card = 544 := by
  simpa using combineTwinPrimeSegments (by decide : 34209837 ≤ 34275373)
    (by decide : 34275373 ≤ 34340909) join_0_0 join_0_1

theorem total : (twinPrimeSegment 34209837 34340909).card = 544 := join_1_0

end S016C05
end Sude.GeneratedTwinScan
