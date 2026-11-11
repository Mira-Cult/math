import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinGeometricScan

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S019C13
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def widths0 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked0 : geometricActiveStreamingTwinScan finiteTwinCheckedBase 41549869 widths0 = 124 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 41549869 41582637).card = 124 := by
  have h := geometricActiveStreamingTwinScan_spec finiteTwinCheckedBase 32768 41549869 widths0
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [checked0] at h
  simpa [widths0] using h.symm

def widths1 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked1 : geometricActiveStreamingTwinScan finiteTwinCheckedBase 41582637 widths1 = 143 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 41582637 41615405).card = 143 := by
  have h := geometricActiveStreamingTwinScan_spec finiteTwinCheckedBase 32768 41582637 widths1
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [checked1] at h
  simpa [widths1] using h.symm

def widths2 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked2 : geometricActiveStreamingTwinScan finiteTwinCheckedBase 41615405 widths2 = 133 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 41615405 41648173).card = 133 := by
  have h := geometricActiveStreamingTwinScan_spec finiteTwinCheckedBase 32768 41615405 widths2
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [checked2] at h
  simpa [widths2] using h.symm

def widths3 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked3 : geometricActiveStreamingTwinScan finiteTwinCheckedBase 41648173 widths3 = 140 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 41648173 41680941).card = 140 := by
  have h := geometricActiveStreamingTwinScan_spec finiteTwinCheckedBase 32768 41648173 widths3
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [checked3] at h
  simpa [widths3] using h.symm

theorem join_0_0 : (twinPrimeSegment 41549869 41615405).card = 267 := by
  simpa using combineTwinPrimeSegments (by decide : 41549869 ≤ 41582637)
    (by decide : 41582637 ≤ 41615405) block0 block1

theorem join_0_1 : (twinPrimeSegment 41615405 41680941).card = 273 := by
  simpa using combineTwinPrimeSegments (by decide : 41615405 ≤ 41648173)
    (by decide : 41648173 ≤ 41680941) block2 block3

theorem join_1_0 : (twinPrimeSegment 41549869 41680941).card = 540 := by
  simpa using combineTwinPrimeSegments (by decide : 41549869 ≤ 41615405)
    (by decide : 41615405 ≤ 41680941) join_0_0 join_0_1

theorem total : (twinPrimeSegment 41549869 41680941).card = 540 := join_1_0

end S019C13
end Sude.GeneratedTwinScan
