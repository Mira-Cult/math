import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinGeometricScan

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S021C12
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def widths0 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked0 : geometricActiveStreamingTwinScan finiteTwinCheckedBase 45613101 widths0 = 150 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 45613101 45645869).card = 150 := by
  have h := geometricActiveStreamingTwinScan_spec finiteTwinCheckedBase 32768 45613101 widths0
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [checked0] at h
  simpa [widths0] using h.symm

def widths1 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked1 : geometricActiveStreamingTwinScan finiteTwinCheckedBase 45645869 widths1 = 142 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 45645869 45678637).card = 142 := by
  have h := geometricActiveStreamingTwinScan_spec finiteTwinCheckedBase 32768 45645869 widths1
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [checked1] at h
  simpa [widths1] using h.symm

def widths2 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked2 : geometricActiveStreamingTwinScan finiteTwinCheckedBase 45678637 widths2 = 156 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 45678637 45711405).card = 156 := by
  have h := geometricActiveStreamingTwinScan_spec finiteTwinCheckedBase 32768 45678637 widths2
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [checked2] at h
  simpa [widths2] using h.symm

def widths3 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked3 : geometricActiveStreamingTwinScan finiteTwinCheckedBase 45711405 widths3 = 138 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 45711405 45744173).card = 138 := by
  have h := geometricActiveStreamingTwinScan_spec finiteTwinCheckedBase 32768 45711405 widths3
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [checked3] at h
  simpa [widths3] using h.symm

theorem join_0_0 : (twinPrimeSegment 45613101 45678637).card = 292 := by
  simpa using combineTwinPrimeSegments (by decide : 45613101 ≤ 45645869)
    (by decide : 45645869 ≤ 45678637) block0 block1

theorem join_0_1 : (twinPrimeSegment 45678637 45744173).card = 294 := by
  simpa using combineTwinPrimeSegments (by decide : 45678637 ≤ 45711405)
    (by decide : 45711405 ≤ 45744173) block2 block3

theorem join_1_0 : (twinPrimeSegment 45613101 45744173).card = 586 := by
  simpa using combineTwinPrimeSegments (by decide : 45613101 ≤ 45678637)
    (by decide : 45678637 ≤ 45744173) join_0_0 join_0_1

theorem total : (twinPrimeSegment 45613101 45744173).card = 586 := join_1_0

end S021C12
end Sude.GeneratedTwinScan
