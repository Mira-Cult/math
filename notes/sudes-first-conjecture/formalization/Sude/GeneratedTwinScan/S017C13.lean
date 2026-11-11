import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinGeometricScan

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S017C13
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def widths0 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked0 : geometricActiveStreamingTwinScan finiteTwinCheckedBase 37355565 widths0 = 143 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 37355565 37388333).card = 143 := by
  have h := geometricActiveStreamingTwinScan_spec finiteTwinCheckedBase 32768 37355565 widths0
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [checked0] at h
  simpa [widths0] using h.symm

def widths1 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked1 : geometricActiveStreamingTwinScan finiteTwinCheckedBase 37388333 widths1 = 154 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 37388333 37421101).card = 154 := by
  have h := geometricActiveStreamingTwinScan_spec finiteTwinCheckedBase 32768 37388333 widths1
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [checked1] at h
  simpa [widths1] using h.symm

def widths2 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked2 : geometricActiveStreamingTwinScan finiteTwinCheckedBase 37421101 widths2 = 139 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 37421101 37453869).card = 139 := by
  have h := geometricActiveStreamingTwinScan_spec finiteTwinCheckedBase 32768 37421101 widths2
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [checked2] at h
  simpa [widths2] using h.symm

def widths3 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked3 : geometricActiveStreamingTwinScan finiteTwinCheckedBase 37453869 widths3 = 155 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 37453869 37486637).card = 155 := by
  have h := geometricActiveStreamingTwinScan_spec finiteTwinCheckedBase 32768 37453869 widths3
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [checked3] at h
  simpa [widths3] using h.symm

theorem join_0_0 : (twinPrimeSegment 37355565 37421101).card = 297 := by
  simpa using combineTwinPrimeSegments (by decide : 37355565 ≤ 37388333)
    (by decide : 37388333 ≤ 37421101) block0 block1

theorem join_0_1 : (twinPrimeSegment 37421101 37486637).card = 294 := by
  simpa using combineTwinPrimeSegments (by decide : 37421101 ≤ 37453869)
    (by decide : 37453869 ≤ 37486637) block2 block3

theorem join_1_0 : (twinPrimeSegment 37355565 37486637).card = 591 := by
  simpa using combineTwinPrimeSegments (by decide : 37355565 ≤ 37421101)
    (by decide : 37421101 ≤ 37486637) join_0_0 join_0_1

theorem total : (twinPrimeSegment 37355565 37486637).card = 591 := join_1_0

end S017C13
end Sude.GeneratedTwinScan
