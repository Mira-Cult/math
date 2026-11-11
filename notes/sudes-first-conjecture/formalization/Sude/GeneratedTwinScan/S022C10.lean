import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinGeometricScan

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S022C10
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def widths0 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked0 : geometricActiveStreamingTwinScan finiteTwinCheckedBase 47448109 widths0 = 160 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 47448109 47480877).card = 160 := by
  have h := geometricActiveStreamingTwinScan_spec finiteTwinCheckedBase 32768 47448109 widths0
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [checked0] at h
  simpa [widths0] using h.symm

def widths1 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked1 : geometricActiveStreamingTwinScan finiteTwinCheckedBase 47480877 widths1 = 125 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 47480877 47513645).card = 125 := by
  have h := geometricActiveStreamingTwinScan_spec finiteTwinCheckedBase 32768 47480877 widths1
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [checked1] at h
  simpa [widths1] using h.symm

def widths2 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked2 : geometricActiveStreamingTwinScan finiteTwinCheckedBase 47513645 widths2 = 138 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 47513645 47546413).card = 138 := by
  have h := geometricActiveStreamingTwinScan_spec finiteTwinCheckedBase 32768 47513645 widths2
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [checked2] at h
  simpa [widths2] using h.symm

def widths3 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked3 : geometricActiveStreamingTwinScan finiteTwinCheckedBase 47546413 widths3 = 130 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 47546413 47579181).card = 130 := by
  have h := geometricActiveStreamingTwinScan_spec finiteTwinCheckedBase 32768 47546413 widths3
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [checked3] at h
  simpa [widths3] using h.symm

theorem join_0_0 : (twinPrimeSegment 47448109 47513645).card = 285 := by
  simpa using combineTwinPrimeSegments (by decide : 47448109 ≤ 47480877)
    (by decide : 47480877 ≤ 47513645) block0 block1

theorem join_0_1 : (twinPrimeSegment 47513645 47579181).card = 268 := by
  simpa using combineTwinPrimeSegments (by decide : 47513645 ≤ 47546413)
    (by decide : 47546413 ≤ 47579181) block2 block3

theorem join_1_0 : (twinPrimeSegment 47448109 47579181).card = 553 := by
  simpa using combineTwinPrimeSegments (by decide : 47448109 ≤ 47513645)
    (by decide : 47513645 ≤ 47579181) join_0_0 join_0_1

theorem total : (twinPrimeSegment 47448109 47579181).card = 553 := join_1_0

end S022C10
end Sude.GeneratedTwinScan
