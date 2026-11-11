import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinGeometricScan

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S022C00
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def widths0 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked0 : geometricActiveStreamingTwinScan finiteTwinCheckedBase 46137389 widths0 = 125 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 46137389 46170157).card = 125 := by
  have h := geometricActiveStreamingTwinScan_spec finiteTwinCheckedBase 32768 46137389 widths0
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [checked0] at h
  simpa [widths0] using h.symm

def widths1 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked1 : geometricActiveStreamingTwinScan finiteTwinCheckedBase 46170157 widths1 = 151 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 46170157 46202925).card = 151 := by
  have h := geometricActiveStreamingTwinScan_spec finiteTwinCheckedBase 32768 46170157 widths1
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [checked1] at h
  simpa [widths1] using h.symm

def widths2 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked2 : geometricActiveStreamingTwinScan finiteTwinCheckedBase 46202925 widths2 = 138 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 46202925 46235693).card = 138 := by
  have h := geometricActiveStreamingTwinScan_spec finiteTwinCheckedBase 32768 46202925 widths2
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [checked2] at h
  simpa [widths2] using h.symm

def widths3 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked3 : geometricActiveStreamingTwinScan finiteTwinCheckedBase 46235693 widths3 = 109 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 46235693 46268461).card = 109 := by
  have h := geometricActiveStreamingTwinScan_spec finiteTwinCheckedBase 32768 46235693 widths3
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [checked3] at h
  simpa [widths3] using h.symm

theorem join_0_0 : (twinPrimeSegment 46137389 46202925).card = 276 := by
  simpa using combineTwinPrimeSegments (by decide : 46137389 ≤ 46170157)
    (by decide : 46170157 ≤ 46202925) block0 block1

theorem join_0_1 : (twinPrimeSegment 46202925 46268461).card = 247 := by
  simpa using combineTwinPrimeSegments (by decide : 46202925 ≤ 46235693)
    (by decide : 46235693 ≤ 46268461) block2 block3

theorem join_1_0 : (twinPrimeSegment 46137389 46268461).card = 523 := by
  simpa using combineTwinPrimeSegments (by decide : 46137389 ≤ 46202925)
    (by decide : 46202925 ≤ 46268461) join_0_0 join_0_1

theorem total : (twinPrimeSegment 46137389 46268461).card = 523 := join_1_0

end S022C00
end Sude.GeneratedTwinScan
