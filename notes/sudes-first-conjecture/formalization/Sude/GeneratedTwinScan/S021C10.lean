import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinGeometricScan

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S021C10
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def widths0 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked0 : geometricActiveStreamingTwinScan finiteTwinCheckedBase 45350957 widths0 = 144 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 45350957 45383725).card = 144 := by
  have h := geometricActiveStreamingTwinScan_spec finiteTwinCheckedBase 32768 45350957 widths0
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [checked0] at h
  simpa [widths0] using h.symm

def widths1 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked1 : geometricActiveStreamingTwinScan finiteTwinCheckedBase 45383725 widths1 = 131 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 45383725 45416493).card = 131 := by
  have h := geometricActiveStreamingTwinScan_spec finiteTwinCheckedBase 32768 45383725 widths1
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [checked1] at h
  simpa [widths1] using h.symm

def widths2 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked2 : geometricActiveStreamingTwinScan finiteTwinCheckedBase 45416493 widths2 = 134 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 45416493 45449261).card = 134 := by
  have h := geometricActiveStreamingTwinScan_spec finiteTwinCheckedBase 32768 45416493 widths2
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [checked2] at h
  simpa [widths2] using h.symm

def widths3 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked3 : geometricActiveStreamingTwinScan finiteTwinCheckedBase 45449261 widths3 = 149 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 45449261 45482029).card = 149 := by
  have h := geometricActiveStreamingTwinScan_spec finiteTwinCheckedBase 32768 45449261 widths3
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [checked3] at h
  simpa [widths3] using h.symm

theorem join_0_0 : (twinPrimeSegment 45350957 45416493).card = 275 := by
  simpa using combineTwinPrimeSegments (by decide : 45350957 ≤ 45383725)
    (by decide : 45383725 ≤ 45416493) block0 block1

theorem join_0_1 : (twinPrimeSegment 45416493 45482029).card = 283 := by
  simpa using combineTwinPrimeSegments (by decide : 45416493 ≤ 45449261)
    (by decide : 45449261 ≤ 45482029) block2 block3

theorem join_1_0 : (twinPrimeSegment 45350957 45482029).card = 558 := by
  simpa using combineTwinPrimeSegments (by decide : 45350957 ≤ 45416493)
    (by decide : 45416493 ≤ 45482029) join_0_0 join_0_1

theorem total : (twinPrimeSegment 45350957 45482029).card = 558 := join_1_0

end S021C10
end Sude.GeneratedTwinScan
