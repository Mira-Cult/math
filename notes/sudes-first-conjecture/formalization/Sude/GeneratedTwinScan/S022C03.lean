import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinGeometricScan

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S022C03
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def widths0 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked0 : geometricActiveStreamingTwinScan finiteTwinCheckedBase 46530605 widths0 = 138 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 46530605 46563373).card = 138 := by
  have h := geometricActiveStreamingTwinScan_spec finiteTwinCheckedBase 32768 46530605 widths0
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [checked0] at h
  simpa [widths0] using h.symm

def widths1 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked1 : geometricActiveStreamingTwinScan finiteTwinCheckedBase 46563373 widths1 = 143 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 46563373 46596141).card = 143 := by
  have h := geometricActiveStreamingTwinScan_spec finiteTwinCheckedBase 32768 46563373 widths1
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [checked1] at h
  simpa [widths1] using h.symm

def widths2 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked2 : geometricActiveStreamingTwinScan finiteTwinCheckedBase 46596141 widths2 = 160 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 46596141 46628909).card = 160 := by
  have h := geometricActiveStreamingTwinScan_spec finiteTwinCheckedBase 32768 46596141 widths2
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [checked2] at h
  simpa [widths2] using h.symm

def widths3 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked3 : geometricActiveStreamingTwinScan finiteTwinCheckedBase 46628909 widths3 = 125 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 46628909 46661677).card = 125 := by
  have h := geometricActiveStreamingTwinScan_spec finiteTwinCheckedBase 32768 46628909 widths3
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [checked3] at h
  simpa [widths3] using h.symm

theorem join_0_0 : (twinPrimeSegment 46530605 46596141).card = 281 := by
  simpa using combineTwinPrimeSegments (by decide : 46530605 ≤ 46563373)
    (by decide : 46563373 ≤ 46596141) block0 block1

theorem join_0_1 : (twinPrimeSegment 46596141 46661677).card = 285 := by
  simpa using combineTwinPrimeSegments (by decide : 46596141 ≤ 46628909)
    (by decide : 46628909 ≤ 46661677) block2 block3

theorem join_1_0 : (twinPrimeSegment 46530605 46661677).card = 566 := by
  simpa using combineTwinPrimeSegments (by decide : 46530605 ≤ 46596141)
    (by decide : 46596141 ≤ 46661677) join_0_0 join_0_1

theorem total : (twinPrimeSegment 46530605 46661677).card = 566 := join_1_0

end S022C03
end Sude.GeneratedTwinScan
