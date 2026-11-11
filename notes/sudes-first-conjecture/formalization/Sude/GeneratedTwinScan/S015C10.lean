import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinGeometricScan

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S015C10
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def widths0 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked0 : geometricActiveStreamingTwinScan finiteTwinCheckedBase 32768045 widths0 = 130 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 32768045 32800813).card = 130 := by
  have h := geometricActiveStreamingTwinScan_spec finiteTwinCheckedBase 32768 32768045 widths0
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [checked0] at h
  simpa [widths0] using h.symm

def widths1 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked1 : geometricActiveStreamingTwinScan finiteTwinCheckedBase 32800813 widths1 = 128 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 32800813 32833581).card = 128 := by
  have h := geometricActiveStreamingTwinScan_spec finiteTwinCheckedBase 32768 32800813 widths1
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [checked1] at h
  simpa [widths1] using h.symm

def widths2 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked2 : geometricActiveStreamingTwinScan finiteTwinCheckedBase 32833581 widths2 = 171 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 32833581 32866349).card = 171 := by
  have h := geometricActiveStreamingTwinScan_spec finiteTwinCheckedBase 32768 32833581 widths2
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [checked2] at h
  simpa [widths2] using h.symm

def widths3 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked3 : geometricActiveStreamingTwinScan finiteTwinCheckedBase 32866349 widths3 = 153 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 32866349 32899117).card = 153 := by
  have h := geometricActiveStreamingTwinScan_spec finiteTwinCheckedBase 32768 32866349 widths3
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [checked3] at h
  simpa [widths3] using h.symm

theorem join_0_0 : (twinPrimeSegment 32768045 32833581).card = 258 := by
  simpa using combineTwinPrimeSegments (by decide : 32768045 ≤ 32800813)
    (by decide : 32800813 ≤ 32833581) block0 block1

theorem join_0_1 : (twinPrimeSegment 32833581 32899117).card = 324 := by
  simpa using combineTwinPrimeSegments (by decide : 32833581 ≤ 32866349)
    (by decide : 32866349 ≤ 32899117) block2 block3

theorem join_1_0 : (twinPrimeSegment 32768045 32899117).card = 582 := by
  simpa using combineTwinPrimeSegments (by decide : 32768045 ≤ 32833581)
    (by decide : 32833581 ≤ 32899117) join_0_0 join_0_1

theorem total : (twinPrimeSegment 32768045 32899117).card = 582 := join_1_0

end S015C10
end Sude.GeneratedTwinScan
