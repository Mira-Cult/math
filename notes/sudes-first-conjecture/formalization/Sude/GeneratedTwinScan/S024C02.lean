import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinGeometricScan

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S024C02
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def widths0 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked0 : geometricActiveStreamingTwinScan finiteTwinCheckedBase 50593837 widths0 = 135 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 50593837 50626605).card = 135 := by
  have h := geometricActiveStreamingTwinScan_spec finiteTwinCheckedBase 32768 50593837 widths0
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [checked0] at h
  simpa [widths0] using h.symm

def widths1 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked1 : geometricActiveStreamingTwinScan finiteTwinCheckedBase 50626605 widths1 = 121 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 50626605 50659373).card = 121 := by
  have h := geometricActiveStreamingTwinScan_spec finiteTwinCheckedBase 32768 50626605 widths1
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [checked1] at h
  simpa [widths1] using h.symm

def widths2 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked2 : geometricActiveStreamingTwinScan finiteTwinCheckedBase 50659373 widths2 = 125 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 50659373 50692141).card = 125 := by
  have h := geometricActiveStreamingTwinScan_spec finiteTwinCheckedBase 32768 50659373 widths2
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [checked2] at h
  simpa [widths2] using h.symm

def widths3 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked3 : geometricActiveStreamingTwinScan finiteTwinCheckedBase 50692141 widths3 = 114 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 50692141 50724909).card = 114 := by
  have h := geometricActiveStreamingTwinScan_spec finiteTwinCheckedBase 32768 50692141 widths3
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [checked3] at h
  simpa [widths3] using h.symm

theorem join_0_0 : (twinPrimeSegment 50593837 50659373).card = 256 := by
  simpa using combineTwinPrimeSegments (by decide : 50593837 ≤ 50626605)
    (by decide : 50626605 ≤ 50659373) block0 block1

theorem join_0_1 : (twinPrimeSegment 50659373 50724909).card = 239 := by
  simpa using combineTwinPrimeSegments (by decide : 50659373 ≤ 50692141)
    (by decide : 50692141 ≤ 50724909) block2 block3

theorem join_1_0 : (twinPrimeSegment 50593837 50724909).card = 495 := by
  simpa using combineTwinPrimeSegments (by decide : 50593837 ≤ 50659373)
    (by decide : 50659373 ≤ 50724909) join_0_0 join_0_1

theorem total : (twinPrimeSegment 50593837 50724909).card = 495 := join_1_0

end S024C02
end Sude.GeneratedTwinScan
