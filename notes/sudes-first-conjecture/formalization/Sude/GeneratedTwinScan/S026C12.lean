import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinGeometricScan

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S026C12
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def widths0 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked0 : geometricActiveStreamingTwinScan finiteTwinCheckedBase 56098861 widths0 = 146 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 56098861 56131629).card = 146 := by
  have h := geometricActiveStreamingTwinScan_spec finiteTwinCheckedBase 32768 56098861 widths0
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [checked0] at h
  simpa [widths0] using h.symm

def widths1 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked1 : geometricActiveStreamingTwinScan finiteTwinCheckedBase 56131629 widths1 = 145 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 56131629 56164397).card = 145 := by
  have h := geometricActiveStreamingTwinScan_spec finiteTwinCheckedBase 32768 56131629 widths1
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [checked1] at h
  simpa [widths1] using h.symm

def widths2 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked2 : geometricActiveStreamingTwinScan finiteTwinCheckedBase 56164397 widths2 = 135 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 56164397 56197165).card = 135 := by
  have h := geometricActiveStreamingTwinScan_spec finiteTwinCheckedBase 32768 56164397 widths2
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [checked2] at h
  simpa [widths2] using h.symm

def widths3 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked3 : geometricActiveStreamingTwinScan finiteTwinCheckedBase 56197165 widths3 = 143 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 56197165 56229933).card = 143 := by
  have h := geometricActiveStreamingTwinScan_spec finiteTwinCheckedBase 32768 56197165 widths3
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [checked3] at h
  simpa [widths3] using h.symm

theorem join_0_0 : (twinPrimeSegment 56098861 56164397).card = 291 := by
  simpa using combineTwinPrimeSegments (by decide : 56098861 ≤ 56131629)
    (by decide : 56131629 ≤ 56164397) block0 block1

theorem join_0_1 : (twinPrimeSegment 56164397 56229933).card = 278 := by
  simpa using combineTwinPrimeSegments (by decide : 56164397 ≤ 56197165)
    (by decide : 56197165 ≤ 56229933) block2 block3

theorem join_1_0 : (twinPrimeSegment 56098861 56229933).card = 569 := by
  simpa using combineTwinPrimeSegments (by decide : 56098861 ≤ 56164397)
    (by decide : 56164397 ≤ 56229933) join_0_0 join_0_1

theorem total : (twinPrimeSegment 56098861 56229933).card = 569 := join_1_0

end S026C12
end Sude.GeneratedTwinScan
