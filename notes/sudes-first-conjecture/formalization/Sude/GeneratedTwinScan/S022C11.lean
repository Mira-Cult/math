import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinGeometricScan

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S022C11
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def widths0 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked0 : geometricActiveStreamingTwinScan finiteTwinCheckedBase 47579181 widths0 = 140 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 47579181 47611949).card = 140 := by
  have h := geometricActiveStreamingTwinScan_spec finiteTwinCheckedBase 32768 47579181 widths0
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [checked0] at h
  simpa [widths0] using h.symm

def widths1 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked1 : geometricActiveStreamingTwinScan finiteTwinCheckedBase 47611949 widths1 = 144 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 47611949 47644717).card = 144 := by
  have h := geometricActiveStreamingTwinScan_spec finiteTwinCheckedBase 32768 47611949 widths1
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [checked1] at h
  simpa [widths1] using h.symm

def widths2 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked2 : geometricActiveStreamingTwinScan finiteTwinCheckedBase 47644717 widths2 = 126 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 47644717 47677485).card = 126 := by
  have h := geometricActiveStreamingTwinScan_spec finiteTwinCheckedBase 32768 47644717 widths2
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [checked2] at h
  simpa [widths2] using h.symm

def widths3 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked3 : geometricActiveStreamingTwinScan finiteTwinCheckedBase 47677485 widths3 = 137 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 47677485 47710253).card = 137 := by
  have h := geometricActiveStreamingTwinScan_spec finiteTwinCheckedBase 32768 47677485 widths3
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [checked3] at h
  simpa [widths3] using h.symm

theorem join_0_0 : (twinPrimeSegment 47579181 47644717).card = 284 := by
  simpa using combineTwinPrimeSegments (by decide : 47579181 ≤ 47611949)
    (by decide : 47611949 ≤ 47644717) block0 block1

theorem join_0_1 : (twinPrimeSegment 47644717 47710253).card = 263 := by
  simpa using combineTwinPrimeSegments (by decide : 47644717 ≤ 47677485)
    (by decide : 47677485 ≤ 47710253) block2 block3

theorem join_1_0 : (twinPrimeSegment 47579181 47710253).card = 547 := by
  simpa using combineTwinPrimeSegments (by decide : 47579181 ≤ 47644717)
    (by decide : 47644717 ≤ 47710253) join_0_0 join_0_1

theorem total : (twinPrimeSegment 47579181 47710253).card = 547 := join_1_0

end S022C11
end Sude.GeneratedTwinScan
