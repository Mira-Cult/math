import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinGeometricScan

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S019C09
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def widths0 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked0 : geometricActiveStreamingTwinScan finiteTwinCheckedBase 41025581 widths0 = 150 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 41025581 41058349).card = 150 := by
  have h := geometricActiveStreamingTwinScan_spec finiteTwinCheckedBase 32768 41025581 widths0
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [checked0] at h
  simpa [widths0] using h.symm

def widths1 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked1 : geometricActiveStreamingTwinScan finiteTwinCheckedBase 41058349 widths1 = 137 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 41058349 41091117).card = 137 := by
  have h := geometricActiveStreamingTwinScan_spec finiteTwinCheckedBase 32768 41058349 widths1
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [checked1] at h
  simpa [widths1] using h.symm

def widths2 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked2 : geometricActiveStreamingTwinScan finiteTwinCheckedBase 41091117 widths2 = 135 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 41091117 41123885).card = 135 := by
  have h := geometricActiveStreamingTwinScan_spec finiteTwinCheckedBase 32768 41091117 widths2
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [checked2] at h
  simpa [widths2] using h.symm

def widths3 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked3 : geometricActiveStreamingTwinScan finiteTwinCheckedBase 41123885 widths3 = 144 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 41123885 41156653).card = 144 := by
  have h := geometricActiveStreamingTwinScan_spec finiteTwinCheckedBase 32768 41123885 widths3
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [checked3] at h
  simpa [widths3] using h.symm

theorem join_0_0 : (twinPrimeSegment 41025581 41091117).card = 287 := by
  simpa using combineTwinPrimeSegments (by decide : 41025581 ≤ 41058349)
    (by decide : 41058349 ≤ 41091117) block0 block1

theorem join_0_1 : (twinPrimeSegment 41091117 41156653).card = 279 := by
  simpa using combineTwinPrimeSegments (by decide : 41091117 ≤ 41123885)
    (by decide : 41123885 ≤ 41156653) block2 block3

theorem join_1_0 : (twinPrimeSegment 41025581 41156653).card = 566 := by
  simpa using combineTwinPrimeSegments (by decide : 41025581 ≤ 41091117)
    (by decide : 41091117 ≤ 41156653) join_0_0 join_0_1

theorem total : (twinPrimeSegment 41025581 41156653).card = 566 := join_1_0

end S019C09
end Sude.GeneratedTwinScan
