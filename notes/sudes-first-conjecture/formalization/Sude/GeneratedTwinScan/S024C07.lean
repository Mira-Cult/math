import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinGeometricScan

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S024C07
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def widths0 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked0 : geometricActiveStreamingTwinScan finiteTwinCheckedBase 51249197 widths0 = 137 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 51249197 51281965).card = 137 := by
  have h := geometricActiveStreamingTwinScan_spec finiteTwinCheckedBase 32768 51249197 widths0
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [checked0] at h
  simpa [widths0] using h.symm

def widths1 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked1 : geometricActiveStreamingTwinScan finiteTwinCheckedBase 51281965 widths1 = 109 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 51281965 51314733).card = 109 := by
  have h := geometricActiveStreamingTwinScan_spec finiteTwinCheckedBase 32768 51281965 widths1
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [checked1] at h
  simpa [widths1] using h.symm

def widths2 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked2 : geometricActiveStreamingTwinScan finiteTwinCheckedBase 51314733 widths2 = 129 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 51314733 51347501).card = 129 := by
  have h := geometricActiveStreamingTwinScan_spec finiteTwinCheckedBase 32768 51314733 widths2
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [checked2] at h
  simpa [widths2] using h.symm

def widths3 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked3 : geometricActiveStreamingTwinScan finiteTwinCheckedBase 51347501 widths3 = 154 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 51347501 51380269).card = 154 := by
  have h := geometricActiveStreamingTwinScan_spec finiteTwinCheckedBase 32768 51347501 widths3
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [checked3] at h
  simpa [widths3] using h.symm

theorem join_0_0 : (twinPrimeSegment 51249197 51314733).card = 246 := by
  simpa using combineTwinPrimeSegments (by decide : 51249197 ≤ 51281965)
    (by decide : 51281965 ≤ 51314733) block0 block1

theorem join_0_1 : (twinPrimeSegment 51314733 51380269).card = 283 := by
  simpa using combineTwinPrimeSegments (by decide : 51314733 ≤ 51347501)
    (by decide : 51347501 ≤ 51380269) block2 block3

theorem join_1_0 : (twinPrimeSegment 51249197 51380269).card = 529 := by
  simpa using combineTwinPrimeSegments (by decide : 51249197 ≤ 51314733)
    (by decide : 51314733 ≤ 51380269) join_0_0 join_0_1

theorem total : (twinPrimeSegment 51249197 51380269).card = 529 := join_1_0

end S024C07
end Sude.GeneratedTwinScan
